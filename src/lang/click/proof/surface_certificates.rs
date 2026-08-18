use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_surface_atomic_derivation(
    replay: &TacticReplayState,
    derivation: &PropositionDerivation,
    preferred_conclusion: Option<&ClickProposition>,
    anchor_point: Option<&ProgramPointRef>,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(ClickProposition, SourceProof), ClickError> {
    let mut conclusion = match preferred_conclusion {
        Some(conclusion) => conclusion.clone(),
        None => crate::instrumentation::measure_operation(
            "have",
            "atomic derivation lowering",
            "derivation lowering: conclusion spelling",
            || {
                checked_surface_fact_at_point(
                    replay,
                    derivation.conclusion(),
                    available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
            },
        )?,
    };
    if let Some(point) = anchor_point {
        conclusion = surface_with_source_site(&conclusion, point)?;
    }
    if let (
        Some((left_derivation, right_derivation)),
        ClickProposition::And(surface_left, surface_right),
    ) = (derivation.conjunction_parts(), &conclusion)
    {
        let (left, left_proof) = lower_surface_atomic_derivation(
            replay,
            left_derivation,
            Some(surface_left),
            anchor_point,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )?;
        let (right, right_proof) = lower_surface_atomic_derivation(
            replay,
            right_derivation,
            Some(surface_right),
            anchor_point,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )?;
        let tactics = vec![
            ProofTactic::Have(ProofHave {
                proposition: left,
                proof: left_proof,
            }),
            ProofTactic::Have(ProofHave {
                proposition: right,
                proof: right_proof,
            }),
            ProofTactic::Split,
        ];
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "conjunction derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let (Some(false_proof), ClickProposition::Implies(surface_antecedent, _)) =
        (derivation.false_antecedent_proof(), &conclusion)
    {
        let negated_antecedent = ClickProposition::Not(surface_antecedent.clone());
        let (negated_antecedent, proof) = lower_surface_atomic_derivation(
            replay,
            false_proof,
            Some(&negated_antecedent),
            anchor_point,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        )?;
        let tactics = vec![
            ProofTactic::Have(ProofHave {
                proposition: negated_antecedent.clone(),
                proof,
            }),
            ProofTactic::Intro,
            ProofTactic::Contradiction(negated_antecedent),
        ];
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "false-antecedent derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    let mut premise_pairs = Vec::new();
    let mut unexpressed_premises = Vec::new();
    let premise_spelling_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: premise spelling",
    );
    let parameter_names = parameters
        .iter()
        .map(syntax::C0Parameter::name)
        .collect::<BTreeSet<_>>();
    for premise in derivation.context_premises() {
        match checked_surface_comparison_fact_at_point(
            replay,
            &premise,
            SurfaceFactMatch::ReplayEquivalent,
            available,
            parameters,
            arguments,
            state,
            predicate_environment,
            click_function_environment,
        ) {
            Ok(surface) => {
                let surface = match anchor_point {
                    // Requirement-definedness facts are recorded when the
                    // function context is built. Re-elaborating their
                    // parameter-only expression after resources have been
                    // folded can produce `false`, even though the exact
                    // certified entry fact and its spelling remain
                    // available. Keep that stable spelling so fresh replay
                    // resolves the same recorded fact instead of evaluating
                    // it against the later heap.
                    Some(_)
                        if matches!(
                            &surface,
                            ClickProposition::Defined { expression }
                                if !contract_expression_mentions_c_local(
                                    expression,
                                    &parameter_names,
                                )
                        ) && replay
                            .surface_propositions
                            .available_kernel(&surface, available)
                            == Some(&premise) =>
                    {
                        surface
                    }
                    Some(point) => surface_with_source_site(&surface, point)?,
                    None => surface,
                };
                premise_pairs.push((premise, surface));
            }
            Err(error) => unexpressed_premises.push((premise, error)),
        }
    }
    drop(premise_spelling_span);
    let conclusion_lowering_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: conclusion lowering",
    );
    let lowered_conclusion = lower_point_proposition(
        &conclusion,
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
    .map_err(ClickError::new)?;
    // `normalize()` must also survive a fresh source replay. The full
    // certificate-generation context can materialize both sides of a framed
    // snapshot equality to one term; direct surface facts retain the
    // loadability/effect context needed to lower ordinary memory expressions
    // without borrowing value aliases from proof search.
    drop(conclusion_lowering_span);
    let _normalization_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: context-free normalization check",
    );
    let surface_normalizes_context_free = lower_point_proposition(
        &conclusion,
        &facts_for_direct_surface_lowering(available),
        parameters,
        arguments,
        replay.old_reference_state(state),
        state,
        None,
        &replay.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .is_ok_and(|goal| normalizes_context_free(&goal));
    drop(_normalization_span);
    let replay_kind = |pairs: &[(Proposition, ClickProposition)]| {
        let surface_premises = pairs
            .iter()
            .map(|(_, surface)| {
                replay
                    .surface_propositions
                    .available_kernel(surface, available)
                    .cloned()
                    .map(Ok)
                    .unwrap_or_else(|| {
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
                    })
            })
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        crate::instrumentation::measure_operation(
            "have",
            "atomic derivation lowering",
            "derivation lowering: replay derivation check",
            || {
                check_atomic_premise_derivation_goal(
                    &lowered_conclusion,
                    surface_premises,
                    &lowered_conclusion,
                    available,
                )
            },
        )
        .is_ok()
        .then_some(())
    };
    let typed_order_pairs = recorded_signed_order_pairs(derivation, &premise_pairs);
    let typed_order_plan = typed_order_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| plan_recorded_signed_order_path(&lowered_conclusion, pairs));
    let typed_equality_pairs = recorded_bitvector_equality_pairs(derivation, &premise_pairs);
    let typed_equality_plan = typed_equality_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_bitvector_equality_path(&lowered_conclusion, derivation, pairs)
        });
    let typed_increment_pairs =
        recorded_int32_increment_upper_bound_pairs(derivation, &premise_pairs);
    let typed_increment_plan = typed_increment_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_upper_bound_for_context(&lowered_conclusion, pairs, false)
        });
    let typed_increment_constant_upper_pairs =
        recorded_int32_increment_constant_upper_bound_pairs(derivation, &premise_pairs);
    let typed_increment_constant_upper_plan = typed_increment_constant_upper_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_constant_upper_bound_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_strict_increment_pairs =
        recorded_int32_increment_strictly_increases_pairs(derivation, &premise_pairs);
    let typed_strict_increment_plan = typed_strict_increment_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_strictly_increases_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_one_plus_strict_pairs =
        recorded_int32_one_plus_strictly_increases_pairs(derivation, &premise_pairs);
    let typed_one_plus_strict_plan = typed_one_plus_strict_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_one_plus_strictly_increases_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_increment_definedness_pairs =
        recorded_int32_increment_below_max_is_defined_pairs(derivation, &premise_pairs);
    let typed_increment_definedness_plan = typed_increment_definedness_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_below_max_is_defined_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_one_plus_definedness_pairs =
        recorded_int32_one_plus_below_max_is_defined_pairs(derivation, &premise_pairs);
    let typed_one_plus_definedness_plan = typed_one_plus_definedness_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_one_plus_below_max_is_defined_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_nonnegative_add_pairs =
        recorded_int32_nonnegative_add_within_max_pairs(derivation, &premise_pairs);
    let typed_nonnegative_add_plan = typed_nonnegative_add_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_nonnegative_add_within_max_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_nonnegative_subtract_pairs =
        recorded_int32_nonnegative_subtract_within_value_pairs(derivation, &premise_pairs);
    let typed_nonnegative_subtract_plan = typed_nonnegative_subtract_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_nonnegative_subtract_within_value_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_increment_lower_bound_pairs =
        recorded_int32_increment_lower_bound_pairs(derivation, &premise_pairs);
    let typed_increment_lower_bound_plan = typed_increment_lower_bound_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_lower_bound_for_context(&lowered_conclusion, pairs, false)
        });
    let typed_increment_greater_equal_pairs =
        recorded_int32_increment_greater_equal_lower_bound_pairs(derivation, &premise_pairs);
    let typed_increment_greater_equal_plan = typed_increment_greater_equal_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_greater_equal_lower_bound_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_increment_strict_greater_pairs =
        recorded_int32_increment_strict_greater_lower_bound_pairs(derivation, &premise_pairs);
    let typed_increment_strict_greater_plan = typed_increment_strict_greater_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_strict_greater_lower_bound_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_increment_strict_from_strict_pairs =
        recorded_int32_increment_strict_greater_from_strict_lower_pairs(derivation, &premise_pairs);
    let typed_increment_strict_from_strict_plan = typed_increment_strict_from_strict_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_strict_greater_from_strict_lower_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_increment_preserves_order_pairs =
        recorded_int32_increment_preserves_order_pairs(derivation, &premise_pairs);
    let typed_increment_preserves_order_plan = typed_increment_preserves_order_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_preserves_order_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_positive_predecessor_nonnegative_pairs =
        recorded_int32_positive_predecessor_is_nonnegative_pairs(derivation, &premise_pairs);
    let typed_positive_predecessor_nonnegative_plan = typed_positive_predecessor_nonnegative_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_positive_predecessor_is_nonnegative_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_positive_predecessor_decrease_pairs =
        recorded_int32_positive_predecessor_strictly_decreases_pairs(derivation, &premise_pairs);
    let typed_positive_predecessor_decrease_plan = typed_positive_predecessor_decrease_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_positive_predecessor_strictly_decreases_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_predecessor_upper_bound_pairs =
        recorded_int32_nonnegative_predecessor_upper_bound_pairs(derivation, &premise_pairs);
    let typed_predecessor_upper_bound_plan = typed_predecessor_upper_bound_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_one_le_predecessor_pairs = recorded_int32_one_le_predecessor_is_nonnegative_pairs(
        derivation,
        &premise_pairs,
    )
    .or_else(|| {
        recorded_int32_one_le_predecessor_strictly_decreases_pairs(derivation, &premise_pairs)
    });
    let typed_one_le_predecessor_plan = typed_one_le_predecessor_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_one_le_predecessor_for_context(&lowered_conclusion, pairs, false)
        });
    let typed_le_not_lt_equality_pairs =
        recorded_int32_le_and_not_lt_implies_equality_pairs(derivation, &premise_pairs);
    let typed_le_not_lt_equality_plan = typed_le_not_lt_equality_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_ge_not_gt_equality_pairs =
        recorded_int32_ge_and_not_gt_implies_equality_pairs(derivation, &premise_pairs);
    let typed_ge_not_gt_equality_plan = typed_ge_not_gt_equality_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_ge_and_not_gt_implies_equality_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_positive_nonnegative_pairs =
        recorded_int32_positive_is_nonnegative_pairs(derivation, &premise_pairs);
    let typed_positive_nonnegative_plan = typed_positive_nonnegative_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_positive_is_nonnegative_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_strictly_positive_nonnegative_pairs =
        recorded_int32_strictly_positive_is_nonnegative_pairs(derivation, &premise_pairs);
    let typed_strictly_positive_nonnegative_plan = typed_strictly_positive_nonnegative_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_strictly_positive_is_nonnegative_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_successor_le_pairs =
        recorded_int32_successor_le_implies_lt_pairs(derivation, &premise_pairs);
    let typed_successor_le_plan = typed_successor_le_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_successor_le_implies_lt_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_constant_lower_pairs =
        recorded_int32_constant_lower_bound_weakening_pairs(derivation, &premise_pairs);
    let typed_constant_lower_plan = typed_constant_lower_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_constant_lower_bound_weakening_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_negated_successor_bound_pairs =
        recorded_int32_negated_strict_successor_bound_pairs(derivation, &premise_pairs);
    let typed_negated_successor_bound_plan = typed_negated_successor_bound_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_negated_strict_successor_bound_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_le_neq_strict_pairs =
        recorded_int32_le_and_neq_implies_strict_pairs(derivation, &premise_pairs);
    let typed_le_neq_strict_plan = typed_le_neq_strict_pairs
        .as_ref()
        .filter(|pairs| replay_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_le_and_neq_implies_strict_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_path_spelled = typed_order_plan.is_some()
        || typed_equality_plan.is_some()
        || typed_increment_plan.is_some()
        || typed_increment_constant_upper_plan.is_some()
        || typed_strict_increment_plan.is_some()
        || typed_one_plus_strict_plan.is_some()
        || typed_increment_definedness_plan.is_some()
        || typed_one_plus_definedness_plan.is_some()
        || typed_nonnegative_add_plan.is_some()
        || typed_nonnegative_subtract_plan.is_some()
        || typed_increment_lower_bound_plan.is_some()
        || typed_increment_greater_equal_plan.is_some()
        || typed_increment_strict_greater_plan.is_some()
        || typed_increment_strict_from_strict_plan.is_some()
        || typed_increment_preserves_order_plan.is_some()
        || typed_positive_predecessor_nonnegative_plan.is_some()
        || typed_positive_predecessor_decrease_plan.is_some()
        || typed_predecessor_upper_bound_plan.is_some()
        || typed_one_le_predecessor_plan.is_some()
        || typed_le_not_lt_equality_plan.is_some()
        || typed_ge_not_gt_equality_plan.is_some()
        || typed_positive_nonnegative_plan.is_some()
        || typed_strictly_positive_nonnegative_plan.is_some()
        || typed_successor_le_plan.is_some()
        || typed_constant_lower_plan.is_some()
        || typed_negated_successor_bound_plan.is_some()
        || typed_le_neq_strict_plan.is_some();
    if typed_order_plan.is_some() {
        premise_pairs = typed_order_pairs.expect("a typed order plan retains its path premises");
    } else if typed_equality_plan.is_some() {
        premise_pairs =
            typed_equality_pairs.expect("a typed equality plan retains its path premises");
    } else if typed_increment_plan.is_some() {
        premise_pairs =
            typed_increment_pairs.expect("a typed increment-bound plan retains its exact premise");
    } else if typed_increment_constant_upper_plan.is_some() {
        premise_pairs = typed_increment_constant_upper_pairs
            .expect("a typed increment-constant-bound plan retains its exact premise");
    } else if typed_strict_increment_plan.is_some() {
        premise_pairs = typed_strict_increment_pairs
            .expect("a typed strict-increment plan retains its exact premise");
    } else if typed_one_plus_strict_plan.is_some() {
        premise_pairs = typed_one_plus_strict_pairs
            .expect("a typed one-plus strict-increment plan retains its exact premise");
    } else if typed_increment_definedness_plan.is_some() {
        premise_pairs = typed_increment_definedness_pairs
            .expect("a typed increment-definedness plan retains its exact premise");
    } else if typed_one_plus_definedness_plan.is_some() {
        premise_pairs = typed_one_plus_definedness_pairs
            .expect("a typed one-plus definedness plan retains its exact premise");
    } else if typed_nonnegative_add_plan.is_some() {
        premise_pairs = typed_nonnegative_add_pairs
            .expect("a typed symbolic-add-definedness plan retains both exact premises");
    } else if typed_nonnegative_subtract_plan.is_some() {
        premise_pairs = typed_nonnegative_subtract_pairs
            .expect("a typed symbolic-subtract-definedness plan retains both exact premises");
    } else if typed_increment_lower_bound_plan.is_some() {
        premise_pairs = typed_increment_lower_bound_pairs
            .expect("a typed increment-lower-bound plan retains both exact premises");
    } else if typed_increment_greater_equal_plan.is_some() {
        premise_pairs = typed_increment_greater_equal_pairs
            .expect("a typed greater-equal increment plan retains both exact premises");
    } else if typed_increment_strict_greater_plan.is_some() {
        premise_pairs = typed_increment_strict_greater_pairs
            .expect("a typed strict-greater increment plan retains both exact premises");
    } else if typed_increment_strict_from_strict_plan.is_some() {
        premise_pairs = typed_increment_strict_from_strict_pairs
            .expect("a typed strict-lower increment plan retains both exact premises");
    } else if typed_increment_preserves_order_plan.is_some() {
        premise_pairs = typed_increment_preserves_order_pairs
            .expect("a typed increment-order plan retains both exact premises");
    } else if typed_positive_predecessor_nonnegative_plan.is_some() {
        premise_pairs = typed_positive_predecessor_nonnegative_pairs
            .expect("a typed predecessor-nonnegative plan retains its exact premise");
    } else if typed_positive_predecessor_decrease_plan.is_some() {
        premise_pairs = typed_positive_predecessor_decrease_pairs
            .expect("a typed predecessor-decrease plan retains its exact premise");
    } else if typed_predecessor_upper_bound_plan.is_some() {
        premise_pairs = typed_predecessor_upper_bound_pairs
            .expect("a typed predecessor-upper-bound plan retains both exact premises");
    } else if typed_one_le_predecessor_plan.is_some() {
        premise_pairs = typed_one_le_predecessor_pairs
            .expect("a typed one-le-predecessor plan retains its exact premise");
    } else if typed_le_not_lt_equality_plan.is_some() {
        premise_pairs = typed_le_not_lt_equality_pairs
            .expect("a typed <=/not-< equality plan retains both exact premises");
    } else if typed_ge_not_gt_equality_plan.is_some() {
        premise_pairs = typed_ge_not_gt_equality_pairs
            .expect("a typed >=/not-> equality plan retains both exact premises");
    } else if typed_positive_nonnegative_plan.is_some() {
        premise_pairs = typed_positive_nonnegative_pairs
            .expect("a typed positive-to-nonnegative plan retains its exact premise");
    } else if typed_strictly_positive_nonnegative_plan.is_some() {
        premise_pairs = typed_strictly_positive_nonnegative_pairs
            .expect("a typed strictly-positive-to-nonnegative plan retains its exact premise");
    } else if typed_successor_le_plan.is_some() {
        premise_pairs = typed_successor_le_pairs
            .expect("a typed successor-lower-bound plan retains its exact premise");
    } else if typed_constant_lower_plan.is_some() {
        premise_pairs = typed_constant_lower_pairs
            .expect("a typed constant-lower-bound plan retains its exact premise");
    } else if typed_negated_successor_bound_plan.is_some() {
        premise_pairs = typed_negated_successor_bound_pairs
            .expect("a typed negated successor-bound plan retains its exact premise");
    } else if typed_le_neq_strict_plan.is_some() {
        premise_pairs = typed_le_neq_strict_pairs
            .expect("a typed <=/!= strict-order plan retains both exact premises");
    }
    if !surface_normalizes_context_free
        && !typed_path_spelled
        && (premise_pairs.is_empty() || replay_kind(&premise_pairs).is_none())
    {
        // Internal derivations are minimized before their kernel facts are
        // translated back to Click. A surface spelling can denote a
        // different snapshot at the replay point, so recover from the full
        // expressible context and minimize again in the representation that
        // will actually be checked.
        let _recovery_span = crate::instrumentation::OperationTiming::new(
            "have",
            "atomic derivation lowering",
            "derivation lowering: full-context surface recovery",
        );
        for premise in available {
            if premise_pairs.iter().any(|(kernel, _)| kernel == premise) {
                continue;
            }
            if let Ok(surface) = checked_surface_comparison_fact_at_point(
                replay,
                premise,
                SurfaceFactMatch::ReplayEquivalent,
                available,
                parameters,
                arguments,
                state,
                predicate_environment,
                click_function_environment,
            ) {
                let surface = match anchor_point {
                    Some(point) => surface_with_source_site(&surface, point)?,
                    None => surface,
                };
                if !premise_pairs
                    .iter()
                    .any(|(_, existing)| existing == &surface)
                {
                    premise_pairs.push((premise.clone(), surface));
                }
            }
        }
        // A recovered spelling can reference a C local that has left scope
        // by the outcome point; such a pair would fail certificate replay's
        // own premise lowering, so it is dropped rather than listed. The
        // derivation check below still validates that the surviving
        // premises suffice.
        premise_pairs.retain(|(_, surface)| {
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
                .is_ok()
        });
        if replay_kind(&premise_pairs).is_none() {
            return Err(ClickError::new(format!(
                "surface premises do not replay the atomic derivation of {}\nunexpressed derivation premises: {}",
                describe_pure_fact(&lowered_conclusion, parameters, arguments),
                describe_unexpressed_pure_facts(&unexpressed_premises, parameters, arguments,),
            )));
        }
    }
    if !typed_path_spelled {
        let mut index = 0;
        while index < premise_pairs.len() {
            let mut reduced = premise_pairs.clone();
            reduced.remove(index);
            if reduced.is_empty() && !surface_normalizes_context_free {
                index += 1;
                continue;
            }
            if replay_kind(&reduced).is_some() {
                premise_pairs = reduced;
            } else {
                index += 1;
            }
        }
    }
    if premise_pairs.is_empty() && surface_normalizes_context_free {
        return Ok((
            conclusion,
            SourceProof::Script(vec![ProofTactic::Normalize]),
        ));
    }
    if let Proposition::Not(body) = &lowered_conclusion
        && let Proposition::ConditionIs(condition, expected) = body.as_ref()
        && let Some((_, surface)) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &Proposition::ConditionIs(condition.clone(), !expected))
    {
        let tactics = vec![
            ProofTactic::Intro,
            ProofTactic::Contradiction(surface.clone()),
        ];
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "negation derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_equality_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded bitvector-equality path produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_order_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded signed-order path produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded increment upper-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_constant_upper_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded increment-constant-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_strict_increment_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded strict-increment rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_one_plus_strict_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded one-plus strict-increment rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_definedness_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded increment-definedness rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_one_plus_definedness_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded one-plus definedness rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_nonnegative_add_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded symbolic-add-definedness rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_nonnegative_subtract_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded symbolic-subtract-definedness rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_lower_bound_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded increment-lower-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_greater_equal_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded greater-equal increment rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_strict_greater_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded strict-greater increment rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_strict_from_strict_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded strict-lower increment rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_increment_preserves_order_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded increment-order rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_positive_predecessor_nonnegative_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded predecessor-nonnegative rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_positive_predecessor_decrease_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded predecessor-decrease rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_predecessor_upper_bound_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded predecessor-upper-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_one_le_predecessor_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded one-le-predecessor rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_le_not_lt_equality_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded <=/not-< equality rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_ge_not_gt_equality_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded >=/not-> equality rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_positive_nonnegative_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded positive-to-nonnegative rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_strictly_positive_nonnegative_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded strictly-positive-to-nonnegative rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_successor_le_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded successor-lower-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_constant_lower_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded constant-lower-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_negated_successor_bound_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded negated successor-bound rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_le_neq_strict_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded <=/!= strict-order rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    // A `rewrite` step substitutes the exact terms of its equality, so its
    // premise is usable only when the surface spelling lowers at replay to
    // the same kernel equality the plan rewrote with. A snapshot-bridged
    // spelling (the same fact recorded against an earlier memory) denotes
    // the value only through frame reasoning, which the simple rewrite
    // cannot check; those premises stay available to the transport path.
    let surface_replays_kernel = |kernel: &Proposition, surface: &ClickProposition| {
        replay
            .surface_propositions
            .available_kernel(surface, available)
            .cloned()
            .map(Ok)
            .unwrap_or_else(|| {
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
            })
            .is_ok_and(|lowered| propositions_match_up_to_canonical_loads(&lowered, kernel))
    };
    let mut rewrite_pairs = premise_pairs
        .iter()
        .filter(|(kernel, surface)| surface_replays_kernel(kernel, surface))
        .cloned()
        .collect::<Vec<_>>();
    // The premises the planner selected are already spelled and validated;
    // when they suffice to spell the rewrite chain, the ambient harvest
    // below never runs. Attributed measurement showed that harvest spelling
    // every ambient equality cost ninety-seven percent of one certificate
    // construction before this ordering.
    if let Some(tactics) =
        plan_explicit_equality_rewrites(&lowered_conclusion, &rewrite_pairs, available)
    {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "atomic derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    let _harvest_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: ambient rewrite harvest",
    );
    // Atomic premise minimization can legitimately discard an execution
    // equality after the kernel has used it to resolve a named local to the
    // arithmetic term that a selected order rule proves. Certificate
    // construction still needs that equality to spell the rewrite from the
    // surface goal. Recover only exact, replayable int32 equalities from the
    // available state; the rewrite planner retains only the ones it selects.
    for premise in available {
        if !matches!(
            premise,
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
        ) || rewrite_pairs.iter().any(|(kernel, _)| kernel == premise)
        {
            continue;
        }
        let Ok(surface) = checked_surface_comparison_fact_at_point(
            replay,
            premise,
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
        let surface = match anchor_point {
            Some(point) => surface_with_source_site(&surface, point)?,
            None => surface,
        };
        if surface_replays_kernel(premise, &surface) {
            rewrite_pairs.push((premise.clone(), surface));
        }
    }
    if let Some(tactics) =
        plan_explicit_equality_rewrites(&lowered_conclusion, &rewrite_pairs, available)
    {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "atomic derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = plan_explicit_named_signed_rule(&lowered_conclusion, &premise_pairs) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "atomic predecessor derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = plan_explicit_increment_lower_bound_transport(
        &lowered_conclusion,
        &conclusion,
        &premise_pairs,
    ) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "increment transport produced a non-simple atomic derivation: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = plan_explicit_forall_instantiation(&lowered_conclusion, &premise_pairs) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "universal instantiation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = plan_explicit_forall_goal(
        &lowered_conclusion,
        &conclusion,
        &premise_pairs,
        available,
        &replay.effect_facts,
        state,
    ) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "universal goal discharge produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    let _rewrites_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: equality rewrite planning",
    );
    if let Some(tactics) = plan_explicit_equality_rewrites_then(
        &lowered_conclusion,
        &rewrite_pairs,
        available,
        &|goal| plan_explicit_named_signed_rule(goal, &premise_pairs),
    ) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "rewritten atomic derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    drop(_rewrites_span);
    let _transport_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: fact transport planning",
    );
    let transport_recognition = assumptions_from_propositions(available);
    for (_, surface_source) in &premise_pairs {
        let source = replay
            .surface_propositions
            .available_kernel(surface_source, available)
            .cloned()
            .map(Ok)
            .unwrap_or_else(|| {
                lower_point_proposition(
                    surface_source,
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
            });
        let Ok(source) = source else {
            continue;
        };
        if !(propositions_match_up_to_canonical_loads(&source, &lowered_conclusion)
            || condition_polarity_equivalent(&source, &lowered_conclusion)
            || crate::kernel::c_condition_facts_equivalent_for_memory_resolution(
                &source,
                &lowered_conclusion,
                &transport_recognition,
            ))
        {
            continue;
        }
        let Ok(premises) = plan_explicit_fact_transport(
            surface_source,
            &source,
            &lowered_conclusion,
            available,
            &replay.effect_facts,
            parameters,
            arguments,
            replay,
            state,
            predicate_environment,
            click_function_environment,
        ) else {
            continue;
        };
        let mut extracted_premises = Vec::new();
        let mut transport_premises = Vec::new();
        for premise in premises {
            flatten_transport_premise(&premise, &mut extracted_premises, &mut transport_premises);
        }
        let mut tactics = extracted_premises
            .into_iter()
            .map(ProofTactic::Extract)
            .collect::<Vec<_>>();
        tactics.push(ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: conclusion.clone(),
            premises: transport_premises,
        });
        tactics.push(ProofTactic::Assumption);
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "atomic transport produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    let internal = std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some().then(|| {
        format!(
            "\n  kernel goal: {}\n  kernel premises: {}",
            bounded_debug(&lowered_conclusion),
            bounded_debug(
                &premise_pairs
                    .iter()
                    .map(|(kernel, _)| kernel)
                    .collect::<Vec<_>>()
            )
        )
    });
    Err(ClickError::new(format!(
        "smart reasoning found a derivation, but Click has no explicit simple certificate for {}\n  selected premises: {}\n  replayable equality rewrites: {}{}",
        describe_pure_fact(&lowered_conclusion, parameters, arguments),
        premise_pairs
            .iter()
            .map(|(_, surface)| describe_click_proposition(surface))
            .collect::<Vec<_>>()
            .join(", "),
        rewrite_pairs
            .iter()
            .map(|(_, surface)| describe_click_proposition(surface))
            .collect::<Vec<_>>()
            .join(", "),
        internal.as_deref().unwrap_or(""),
    )))
}

fn flatten_transport_premise(
    premise: &ClickProposition,
    extracted: &mut Vec<ClickProposition>,
    leaves: &mut Vec<ClickProposition>,
) {
    let ClickProposition::And(left, right) = premise else {
        leaves.push(premise.clone());
        return;
    };
    for child in [left.as_ref(), right.as_ref()] {
        extracted.push(child.clone());
        flatten_transport_premise(child, extracted, leaves);
    }
}

enum OutcomeSimpSelection {
    Simple(ProofTactic),
    Premises(Vec<ClickProposition>),
}

#[allow(clippy::too_many_arguments)]
fn select_outcome_simp_certificate(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<OutcomeSimpSelection, ClickError> {
    check_verification_deadline()?;
    let check = |surface: &ClickProposition| {
        lower_outcome_proposition_with_program_points(
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            available,
            surface,
            predicate_environment,
            click_function_environment,
            &replay.program_point_states,
        )
    };
    // Kernel planning may already hold a canonicalized snapshot spelling
    // that normalizes reflexively. `normalize` is a valid surface certificate
    // only when lowering the emitted source goal at this exact outcome also
    // normalizes context-free; otherwise replay can see two distinct memory
    // snapshots and needs an explicit derivation instead.
    if matches!(normalize_proposition(goal), SimpProposition::True)
        && check(surface_goal).is_ok_and(|lowered| normalizes_context_free(&lowered))
    {
        return Ok(OutcomeSimpSelection::Simple(ProofTactic::Normalize));
    }
    // A kernel derivation is not yet usable surface evidence: a synthesized
    // premise can lower to a different snapshot spelling during replay.
    // Validate the actual surface premises before handing them to the
    // explicit-certificate planner below.
    let replayable_premises = |premises: Vec<ClickProposition>| {
        let lowered = premises
            .iter()
            .map(&check)
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        let replayable =
            check_atomic_premise_derivation_goal(goal, lowered, goal, available).is_ok();
        replayable.then_some(OutcomeSimpSelection::Premises(premises))
    };
    if check(surface_goal)
        .is_ok_and(|surface_goal| pure_fact_is_replay_available(&surface_goal, available))
    {
        return Ok(OutcomeSimpSelection::Simple(ProofTactic::Assumption));
    }
    let normalized_goal = normalize_direct_atomic_memory_loads(goal);
    let mut atomic_available = Vec::new();
    for fact in available {
        check_verification_deadline()?;
        atomic_conjuncts(fact, &mut atomic_available);
    }
    let atomic_available = atomic_available.into_iter().cloned().collect::<Vec<_>>();
    let source_for_required = |required: &Proposition| {
        let loadability_source = directly_covering_loadability_fact(required, &atomic_available);
        let checked_source = |fact: &Proposition| {
            checked_surface_fact_at_outcome(
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
            )
            .ok()
            .filter(|surface| {
                check(surface).is_ok_and(|lowered| {
                    condition_polarity_equivalent(&lowered, fact)
                        || nested_quantified_binder_equivalent(&lowered, fact, 8)
                })
            })
            .map(|surface| (fact.clone(), surface))
        };

        // Exact facts (and the one preselected covering loadability fact) are
        // overwhelmingly the common case. Do not surface-lower every
        // snapshot-equivalent ambient fact before trying them.
        atomic_available
            .iter()
            .filter(|fact| {
                *fact == required
                    || loadability_source
                        .as_ref()
                        .is_some_and(|source| source == *fact)
            })
            .find_map(&checked_source)
            .or_else(|| {
                atomic_available
                    .iter()
                    .filter(|fact| {
                        condition_polarity_equivalent(
                            &normalize_direct_atomic_memory_loads(fact),
                            &normalize_direct_atomic_memory_loads(required),
                        ) || matches!(
                            (fact, required),
                            (Proposition::ForAll { .. }, Proposition::ForAll { .. })
                        )
                    })
                    .find_map(checked_source)
            })
    };
    let normalized_available = atomic_available
        .iter()
        .map(normalize_direct_atomic_memory_loads)
        .collect::<Vec<_>>();
    // Plan against the kernel facts, then require an exact checked Surface
    // spelling for every premise the derivation actually selected. The
    // derivation context is the complete dependency boundary; eagerly
    // translating every ambient fact is both unnecessary and pathologically
    // expensive when facts contain symbolic memory snapshots.
    if let Some(SimpEvidence::Derivation(derivation)) =
        plan_simp_certificate(goal, &assumptions_from_propositions(&atomic_available))
    {
        let ambient = assumptions_from_propositions(&atomic_available);
        let context = derivation
            .context_premises()
            .into_iter()
            .filter(|premise| {
                !(matches!(normalize_proposition(premise), SimpProposition::True)
                    || matches!(
                        premise,
                        Proposition::CMemoryMutatesOnly { .. }
                            | Proposition::CMemoryEffectSummary { .. }
                            | Proposition::CHeapLifetimeRetired { .. }
                    )
                    // A loadability premise the ambient context re-derives
                    // (for example from materialized memory) needs no
                    // surface spelling; replay re-derives it the same way.
                    || matches!(premise, Proposition::CMemoryLoadable { .. })
                        && ambient.derive_atomic_proposition(premise).is_some())
            })
            .collect::<Vec<_>>();
        let mut selected_premises = Some(Vec::new());
        for required in &context {
            check_verification_deadline()?;
            let Some(selected) = source_for_required(required) else {
                // The kernel planner may select a derived ambient equality
                // whose internal pointer spelling has no Surface Click
                // source. This plan cannot be emitted as a certificate, but
                // the explicit and normalized fallback planners below may
                // still find a replayable dependency boundary.
                selected_premises = None;
                break;
            };
            if let Some(selected_premises) = &mut selected_premises
                && !selected_premises.contains(&selected)
            {
                selected_premises.push(selected);
            }
        }
        if let Some(selected_premises) = selected_premises {
            let selected_kernel = selected_premises
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            if derivation.replay(&assumptions_from_propositions(&selected_kernel)) {
                let premises = selected_premises
                    .into_iter()
                    .map(|(_, surface)| surface)
                    .collect();
                if let Some(selection) = replayable_premises(premises) {
                    return Ok(selection);
                }
            }
        }
    }
    if let Some(derivation) =
        minimal_simp_proposition_derivation(&normalized_goal, &normalized_available)?
    {
        let context = derivation.context_premises();
        let selected = context
            .iter()
            .filter_map(|required| {
                atomic_available.iter().find(|fact| {
                    condition_polarity_equivalent(
                        &normalize_direct_atomic_memory_loads(fact),
                        required,
                    )
                })
            })
            .collect::<Vec<_>>();
        if selected.len() == context.len() {
            let surface_premises = selected
                .iter()
                .map(|fact| {
                    checked_surface_fact_at_outcome(
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
                    )
                })
                .collect::<Result<Vec<_>, _>>();
            if let Ok(surface_premises) = surface_premises
                && let Some(selection) = replayable_premises(surface_premises)
            {
                return Ok(selection);
            }
        }
    }
    let points = replay
        .program_point_states
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    if let Some(variants) = comparison_program_point_variants(surface_goal, &points) {
        for candidate in variants {
            check_verification_deadline()?;
            let Ok(lowered) = check(&candidate) else {
                continue;
            };
            let Some(available_fact) = available
                .iter()
                .find(|fact| condition_polarity_equivalent(fact, &lowered))
                .cloned()
            else {
                continue;
            };
            let assumptions = assumptions_from_propositions(std::slice::from_ref(&available_fact));
            if assumptions.derive_simp_proposition(goal).is_some()
                && let Some(selection) = replayable_premises(vec![candidate])
            {
                return Ok(selection);
            }
        }
    }
    if let Some(fact) = available.iter().find(|fact| {
        condition_polarity_equivalent(
            &normalize_direct_atomic_memory_loads(fact),
            &normalized_goal,
        )
    }) && let Ok(surface) = checked_surface_fact_at_outcome(
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
    ) && check(&surface).is_ok_and(|lowered| condition_polarity_equivalent(&lowered, fact))
    {
        let assumptions = assumptions_from_propositions(std::slice::from_ref(fact));
        if assumptions
            .derive_atomic_proposition(goal)
            .or_else(|| assumptions.derive_proposition(goal))
            .is_some()
            && let Some(selection) = replayable_premises(vec![surface.clone()])
        {
            return Ok(selection);
        }
        if assumptions
            .derive_simp_atomic_proposition(goal)
            .or_else(|| assumptions.derive_simp_proposition(goal))
            .is_some()
            && let Some(selection) = replayable_premises(vec![surface])
        {
            return Ok(selection);
        }
    }
    let mut premise_pairs = Vec::new();
    for fact in available {
        check_verification_deadline()?;
        // Recorded exact spellings are already paired with this kernel fact
        // and avoid a costly synthesis attempt at every retained program
        // point. The completed fallback certificate is still replayed below,
        // so an inapplicable spelling cannot escape validation.
        let surface = replay
            .surface_propositions
            .surfaces(fact)
            .find(|surface| {
                check(surface).is_ok_and(|lowered| {
                    condition_polarity_equivalent(&lowered, fact)
                        || nested_quantified_binder_equivalent(&lowered, fact, 8)
                })
            })
            .cloned()
            .or_else(|| {
                checked_surface_fact_at_outcome(
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
                )
                .ok()
            });
        let Some(surface) = surface else {
            continue;
        };
        if check(&surface).is_ok_and(|lowered| {
            condition_polarity_equivalent(&lowered, fact)
                || nested_quantified_binder_equivalent(&lowered, fact, 8)
        }) && !premise_pairs
            .iter()
            .any(|(kernel, recorded_surface)| kernel == fact || recorded_surface == &surface)
        {
            premise_pairs.push((fact.clone(), surface));
        }
    }
    // Public call postconditions whose symbolic result has since been stored
    // in a C local are deliberately retained as certified effect facts. Give
    // those facts their stable local spelling so ordinary equality reasoning
    // can compose them with later call postconditions. Execution-only call
    // identities remain private because they are neither public nor
    // source-spellable through a local.
    for fact in replay
        .effect_facts
        .iter()
        .filter(|fact| {
            fact.is_public()
                && fact.is_certified()
                && matches!(fact.proposition(), Proposition::ConditionIs(_, _))
        })
        .map(ExecutionPureFact::proposition)
    {
        check_verification_deadline()?;
        if premise_pairs.iter().any(|(kernel, _)| kernel == fact) {
            continue;
        }
        let selected = std::iter::once((None, post_state))
            .chain(
                replay
                    .program_point_states
                    .iter()
                    .rev()
                    .map(|(point, state)| (Some(point), state)),
            )
            .find_map(|(point, state)| {
                let core = synthesize_surface_proposition(fact, parameters, arguments, state)?;
                if !public_local_result_surface(&core, parameters) {
                    return None;
                }
                let surface = match point {
                    None => core,
                    Some(point) => ClickProposition::At {
                        selector: VisitSelector::ProgramPoint(point.clone()),
                        proposition: Box::new(core),
                    },
                };
                let lowered = check(&surface).ok()?;
                condition_polarity_equivalent(&lowered, fact).then_some((surface, lowered))
            });
        let Some((surface, lowered)) = selected else {
            continue;
        };
        premise_pairs.push((lowered, surface));
    }
    // Alias branches created while executing a call are certified execution
    // facts, not source assertions. When a branch condition is needed to
    // close an impossible path, synthesize its exact program-point spelling
    // so the generated certificate can name that dependency.
    for fact in available
        .iter()
        .chain(
            replay
                .effect_facts
                .iter()
                .map(ExecutionPureFact::proposition),
        )
        .filter(|fact| {
            matches!(
                fact,
                Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
            )
        })
    {
        check_verification_deadline()?;
        if premise_pairs.iter().any(|(kernel, _)| kernel == fact) {
            continue;
        }
        let entry_point = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let synthesized = std::iter::once((&entry_point, pre_state))
            .chain(replay.program_point_states.iter().rev())
            .find_map(|(point, state)| {
                let core = synthesize_surface_proposition(fact, parameters, arguments, state)?;
                let surface = ClickProposition::At {
                    selector: VisitSelector::ProgramPoint(point.clone()),
                    proposition: Box::new(core),
                };
                check(&surface)
                    .ok()
                    .filter(|lowered| condition_polarity_equivalent(lowered, fact))
                    .map(|_| surface)
            });
        if let Some(surface) = synthesized {
            premise_pairs.push((fact.clone(), surface));
        }
    }
    let kernel_premises = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let surface_premises = premise_pairs
        .iter()
        .cloned()
        .map(|(_, surface)| surface)
        .collect::<Vec<_>>();
    if surface_premises.is_empty() {
        return Err(ClickError::new(format!(
            "postcondition has no expressible premises for surface `simp` lowering: {goal:?}"
        )));
    }
    let normalized_kernel_premises = kernel_premises
        .iter()
        .map(normalize_direct_atomic_memory_loads)
        .collect::<Vec<_>>();
    let assumptions = assumptions_from_propositions(&normalized_kernel_premises);
    let exact_assumptions = assumptions_from_propositions(&kernel_premises);
    check_verification_deadline()?;
    if let Some(SimpEvidence::Derivation(derivation)) =
        plan_simp_certificate(goal, &assumptions_from_propositions(available))
    {
        let context = derivation.context_premises();
        let selected = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                context
                    .iter()
                    .any(|required| exact_fact_contains_conjunct(kernel, required))
            })
            .cloned()
            .collect::<Vec<_>>();
        let selected_kernel = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        if derivation.replay(&assumptions_from_propositions(&selected_kernel)) {
            let premises = selected.into_iter().map(|(_, surface)| surface).collect();
            if let Some(selection) = replayable_premises(premises) {
                return Ok(selection);
            }
        }
    }
    if ((exact_assumptions
        .derive_atomic_proposition(goal)
        .or_else(|| exact_assumptions.derive_proposition(goal))
        .is_some()
        && assumptions
            .derive_atomic_proposition(&normalized_goal)
            .or_else(|| assumptions.derive_proposition(&normalized_goal))
            .is_some())
        || (exact_assumptions
            .derive_simp_atomic_proposition(goal)
            .or_else(|| exact_assumptions.derive_simp_proposition(goal))
            .is_some()
            && assumptions
                .derive_simp_atomic_proposition(&normalized_goal)
                .or_else(|| assumptions.derive_simp_proposition(&normalized_goal))
                .is_some()))
        && let Some(selection) = replayable_premises(surface_premises.clone())
    {
        return Ok(selection);
    }
    {
        // Effect-backed postconditions derive from kernel-certified facts
        // (statement effect facts and certified store equations). Everything
        // gets a surface spelling: express each premise the minimized
        // derivation needs, synthesizing an `at(point, ...)` spelling from a
        // recorded program-point state when no ambient fact carries it.
        let mut certified_context = available.to_vec();
        for fact in &replay.effect_facts {
            check_verification_deadline()?;
            if !certified_context.contains(fact.proposition()) {
                certified_context.push(fact.proposition().clone());
            }
        }
        let certified_store_equations =
            crate::kernel::certified_store_equations(&replay.effect_facts);
        for equation in &certified_store_equations {
            check_verification_deadline()?;
            if !certified_context.contains(equation) {
                certified_context.push(equation.clone());
            }
        }
        check_verification_deadline()?;
        if check_atomic_premise_derivation_goal(
            goal,
            kernel_premises.clone(),
            goal,
            &certified_context,
        )
        .is_ok()
        {
            return Ok(OutcomeSimpSelection::Premises(surface_premises.clone()));
        }
        let spelled_store_equations = certified_store_equations
            .iter()
            .filter_map(|equation| {
                let surfaces = replay
                    .surface_propositions
                    .surfaces(equation)
                    .collect::<Vec<_>>();
                let surface = surfaces
                    .iter()
                    .find(|surface| {
                        matches!(
                            surface,
                            ClickProposition::Comparison {
                                left: ContractExpression::At { .. },
                                ..
                            }
                        )
                    })
                    .copied()
                    .or_else(|| surfaces.last().copied())?;
                Some((equation.clone(), surface.clone()))
            })
            .collect::<Vec<_>>();
        if spelled_store_equations.len() == certified_store_equations.len()
            && !spelled_store_equations.is_empty()
        {
            let kernel_premises = spelled_store_equations
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            let surface_premises = spelled_store_equations
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            check_verification_deadline()?;
            let checked = check_atomic_premise_derivation_goal(
                goal,
                kernel_premises.clone(),
                goal,
                &certified_context,
            );
            if checked.is_ok() {
                return Ok(OutcomeSimpSelection::Premises(surface_premises));
            }
        }
        check_verification_deadline()?;
        let minimized = match minimal_proposition_derivation(goal, &certified_context)? {
            Some(derivation) => Some(derivation),
            None => minimal_simp_proposition_derivation(goal, &certified_context)?,
        };
        check_verification_deadline()?;
        if let Some(derivation) = minimized {
            let entry_point = ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            };
            let mut spelled_premises: Vec<ClickProposition> = Vec::new();
            let mut kernel_premises: Vec<Proposition> = Vec::new();
            let mut complete = true;
            // A spelling that lowers to a snapshot-variant of the required
            // premise still replays: the closing self-check below validates
            // the actual lowered premises, so a bridged match can only fail
            // closed, never accept a wrong certificate.
            let bridged_match_assumptions = assumptions_from_propositions(&certified_context);
            let bridged_match = |lowered: &Proposition, required: &Proposition| {
                propositions_match_up_to_canonical_loads(lowered, required)
                    || snapshot_bridged_fact_is_available_under(
                        required,
                        std::slice::from_ref(lowered),
                        &bridged_match_assumptions,
                        &[],
                    )
            };
            'premises: for required in derivation.context_premises() {
                check_verification_deadline()?;
                // A recorded spelling is only usable if it still lowers at
                // the outcome. In particular, a bare branch-local name can
                // remain in the planning map after the C local has left
                // scope; the replay map then cannot rescue that dead name.
                if let Ok(surface) = replay.surface_propositions.surface(&required)
                    && let Ok(lowered) = check(surface)
                    && bridged_match(&lowered, &required)
                {
                    if !kernel_premises.contains(&lowered) {
                        kernel_premises.push(lowered);
                        spelled_premises.push(surface.clone());
                    }
                    continue;
                }
                if let Some((surface, lowered)) = available.iter().find_map(|fact| {
                    if !exact_fact_contains_conjunct(fact, &required) {
                        return None;
                    }
                    let surface = checked_surface_fact_at_outcome(
                        replay,
                        fact,
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
                    .ok()?;
                    // Record what the spelling actually lowers to. Canonical
                    // load spelling only recognizes candidates; the replay
                    // below must derive from this exact lowered proposition.
                    let lowered = check(&surface).ok()?;
                    bridged_match(&lowered, &required).then_some((surface, lowered))
                }) {
                    if !kernel_premises.contains(&lowered) {
                        kernel_premises.push(lowered);
                        spelled_premises.push(surface);
                    }
                    continue;
                }
                let candidate_states = std::iter::once((&entry_point, pre_state))
                    .chain(replay.program_point_states.iter().rev());
                for (point, point_state) in candidate_states {
                    check_verification_deadline()?;
                    let Some(core) = synthesize_surface_proposition(
                        &required,
                        parameters,
                        arguments,
                        point_state,
                    ) else {
                        continue;
                    };
                    let surface = ClickProposition::At {
                        selector: VisitSelector::ProgramPoint(point.clone()),
                        proposition: Box::new(core),
                    };
                    if let Ok(lowered) = check(&surface)
                        && (bridged_match(&lowered, &required)
                            // A quantified fact re-lowers with fresh binder
                            // variables; recognize it up to per-level binder
                            // renaming like the ambient premise pairing does.
                            || nested_quantified_binder_equivalent(&lowered, &required, 8))
                    {
                        if !kernel_premises.contains(&lowered) {
                            kernel_premises.push(lowered);
                            spelled_premises.push(surface);
                        }
                        continue 'premises;
                    }
                }
                complete = false;
                break;
            }
            if complete && !spelled_premises.is_empty() {
                // Self-check with exactly the check the tactic replay runs,
                // against the replay context (which carries the certified
                // store equations).
                if check_atomic_premise_derivation_goal(
                    goal,
                    kernel_premises,
                    goal,
                    &certified_context,
                )
                .is_ok()
                {
                    return Ok(OutcomeSimpSelection::Premises(spelled_premises));
                }
            }
        }
        Err(ClickError::new(format!(
            "expressible path facts do not replay the postcondition derivation: {}\n  surface premises: {}",
            bounded_debug(goal),
            surface_premises
                .iter()
                .map(describe_click_proposition)
                .collect::<Vec<_>>()
                .join(", ")
        )))
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_outcome_simp_tactics(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<ProofTactic>, ClickError> {
    let selection = select_outcome_simp_certificate(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?;
    let premises = match selection {
        OutcomeSimpSelection::Simple(tactic) => return Ok(vec![tactic]),
        OutcomeSimpSelection::Premises(premises) => premises,
    };
    let premise_pairs = premises
        .iter()
        .map(|surface| {
            replay
                .surface_propositions
                .available_kernel(surface, available)
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    lower_outcome_proposition_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        available,
                        surface,
                        predicate_environment,
                        click_function_environment,
                        &replay.program_point_states,
                    )
                })
                .map(|kernel| (kernel, surface.clone()))
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(ClickError::new)?;

    // An observed resource-count witness can survive execution as the exact
    // postcondition fact. Its smallest certificate is the ordinary simple
    // assumption rule; routing the identity derivation through arithmetic
    // rewrite planning incorrectly reports that no certificate exists.
    if premise_pairs.iter().any(|(premise, _)| premise == goal) {
        return Ok(vec![ProofTactic::Assumption]);
    }
    if let ClickProposition::PredicateCall { name, .. } = surface_goal {
        let unfolded_goal = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            std::slice::from_ref(name),
            goal,
            &assumptions_from_propositions(&available),
        )
        .map_err(ClickError::new)?;
        if pure_fact_is_replay_available(&unfolded_goal, &available) {
            return Ok(vec![
                ProofTactic::UnfoldPredicate(name.clone()),
                ProofTactic::Assumption,
            ]);
        }
        if let Some(mut suffix) =
            plan_explicit_greater_equal_to_reversed_less_equal(&unfolded_goal, &premise_pairs)
        {
            let mut tactics = vec![ProofTactic::UnfoldPredicate(name.clone())];
            tactics.append(&mut suffix);
            return Ok(tactics);
        }
        // A universal predicate body (such as an `all_le_range` or `sorted`
        // postcondition) is dischargeable through the explicit forall-goal
        // chain or a spelled finite enumeration once the goal is unfolded to
        // its quantified spelling. Nested predicate definitions unfold one
        // named step at a time, and each step is carried in the certificate.
        let mut unfold_names = Vec::new();
        let mut unfolded_surface = surface_goal.clone();
        while let ClickProposition::PredicateCall { name, .. } = &unfolded_surface {
            if unfold_names.len() >= 8 || predicate_environment.get(name).is_none() {
                break;
            }
            let Ok(next) = unfold_structural_invariant_proposition(
                predicate_environment,
                &unfolded_surface,
                std::slice::from_ref(name),
            ) else {
                break;
            };
            unfold_names.push(name.clone());
            unfolded_surface = next;
        }
        if !unfold_names.is_empty()
            && let Ok(fully_unfolded_goal) = unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                &unfold_names,
                goal,
                &assumptions_from_propositions(&available),
            )
        {
            let suffix = plan_explicit_forall_goal(
                &fully_unfolded_goal,
                &unfolded_surface,
                &premise_pairs,
                available,
                &replay.effect_facts,
                post_state,
            )
            .or_else(|| {
                plan_outcome_finite_forall_enumeration(
                    replay,
                    &unfolded_surface,
                    &fully_unfolded_goal,
                    available,
                    &premise_pairs,
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    result,
                    predicate_environment,
                    click_function_environment,
                )
            });
            if let Some(mut suffix) = suffix {
                let mut tactics = unfold_names
                    .into_iter()
                    .map(ProofTactic::UnfoldPredicate)
                    .collect::<Vec<_>>();
                tactics.append(&mut suffix);
                ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                    ClickError::new(format!(
                        "universal predicate goal discharge produced a non-simple expansion: {error:?}"
                    ))
                })?;
                return Ok(tactics);
            }
        }
    }
    if let Some(tactics) = plan_explicit_unchanged_load_transport(
        goal,
        surface_goal,
        &premise_pairs,
        available,
        &replay.effect_facts,
        post_state,
        &[],
    ) {
        return Ok(tactics);
    }
    if let Some(tactics) = plan_explicit_loadability_transport(goal, surface_goal, &premise_pairs) {
        return Ok(tactics);
    }
    if let Some(tactics) =
        plan_explicit_increment_lower_bound_transport(goal, surface_goal, &premise_pairs)
    {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "increment transport produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok(tactics);
    }
    if let Some(tactics) = plan_explicit_forall_instantiation(goal, &premise_pairs) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "universal instantiation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok(tactics);
    }
    if let Some(tactics) = plan_explicit_forall_goal(
        goal,
        surface_goal,
        &premise_pairs,
        available,
        &replay.effect_facts,
        post_state,
    ) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "universal goal discharge produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok(tactics);
    }
    let mut search_pairs = premise_pairs.clone();
    let mut extracted_surfaces = Vec::new();
    for (kernel, surface) in &premise_pairs {
        collect_surface_conjunct_pairs(kernel, surface, &mut search_pairs, &mut extracted_surfaces);
    }
    // One search-time vocabulary: the shared explicit-certificate search with
    // the full named-rule list. A derivation this cannot spell is a failure of
    // the whole tactic, never a post-hoc translation gap.
    if let Some(mut explicit) = plan_explicit_equality_rewrites_from(
        goal,
        &search_pairs,
        available,
        &|current| pure_fact_is_replay_available(current, available),
        &|current| {
            plan_explicit_named_signed_rule(current, &search_pairs).or_else(|| {
                // Outcome `have` bodies admit nested `have` steps, so the
                // predecessor rule may spell its nonnegativity leg here.
                plan_explicit_predecessor_upper_bound(current, &search_pairs, true)
            })
        },
    ) {
        explicit.splice(
            0..0,
            extracted_surfaces.into_iter().map(ProofTactic::Extract),
        );
        Ok(explicit)
    } else if let Some(tactics) = plan_outcome_disjunction_cases(
        replay,
        surface_goal,
        goal,
        available,
        &premise_pairs,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    ) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "disjunction case split produced a non-simple expansion: {error:?}"
            ))
        })?;
        Ok(tactics)
    } else {
        Err(ClickError::new(format!(
            "post-execution simplification proved `{}`, but Click has no explicit simple certificate for that derivation\n  selected premises: {}",
            describe_click_proposition(surface_goal),
            premise_pairs
                .iter()
                .map(|(_, surface)| describe_click_proposition(surface))
                .collect::<Vec<_>>()
                .join(", "),
        )))
    }
}

/// Constructs an explicit `cases` certificate that eliminates one spelled
/// disjunctive premise. Search recurses into each branch with exactly the
/// assumed disjunct added, so the emitted certificate spells both branches
/// and replay checks them under their own assumption only. A premise whose
/// disjunct is already available is skipped, which bounds the recursion by
/// the number of distinct disjunctive premises.
#[allow(clippy::too_many_arguments)]
fn plan_outcome_disjunction_cases(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    premise_pairs: &[(Proposition, ClickProposition)],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Option<Vec<ProofTactic>> {
    for (kernel, surface) in premise_pairs {
        check_verification_deadline().ok()?;
        let Proposition::Or(left, right) = kernel else {
            continue;
        };
        if pure_fact_is_replay_available(left, available)
            || pure_fact_is_replay_available(right, available)
        {
            continue;
        }
        let branch = |disjunct: &Proposition| {
            let mut branch_available = available.to_vec();
            branch_available.push(disjunct.clone());
            match lower_outcome_simp_proof(
                replay,
                surface_goal,
                goal,
                &branch_available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            ) {
                Ok(SourceProof::Script(tactics)) => Some(tactics),
                _ => None,
            }
        };
        let Some(left_tactics) = branch(left) else {
            continue;
        };
        let Some(right_tactics) = branch(right) else {
            continue;
        };
        return Some(vec![ProofTactic::Cases(ProofCases {
            disjunction: surface.clone(),
            left_tactics,
            right_tactics,
        })]);
    }
    None
}

/// Constructs an explicit finite-enumeration certificate for a
/// constant-bounded universal goal: one spelled `have` per non-vacuous
/// instance of the kernel's deterministic instantiation table (each proved by
/// its own recursively constructed certificate), closed by `enumerate()`.
/// Vacuous instances (a guard refuted by the substituted constants) are
/// checked by normalization during replay and need no spelled proof.
#[allow(clippy::too_many_arguments)]
fn plan_outcome_finite_forall_enumeration(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    premise_pairs: &[(Proposition, ClickProposition)],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Option<Vec<ProofTactic>> {
    let instances = crate::kernel::finite_forall_goal_instances(goal)?;
    // Peel the surface binder chain to substitute each enumerated value.
    let mut binder_names = Vec::new();
    let mut surface_body = surface_goal;
    while let ClickProposition::ForAll { name, body, .. } = surface_body {
        binder_names.push(name.clone());
        surface_body = body.as_ref();
    }
    if binder_names.is_empty() {
        return None;
    }
    let mut tactics = Vec::new();
    for (values, instance) in instances {
        check_verification_deadline().ok()?;
        if values.len() != binder_names.len() {
            return None;
        }
        if matches!(normalize_proposition(&instance), SimpProposition::True) {
            continue;
        }
        let value_expressions = values
            .iter()
            .map(|value| {
                u32::try_from(*value).ok().map(|value| {
                    ContractExpression::CFragment(CExpression::Value(int32(
                        Bitvector32Term::Constant(value),
                    )))
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let substitutions = binder_names
            .iter()
            .cloned()
            .zip(value_expressions.iter().cloned())
            .collect::<BTreeMap<_, _>>();
        let surface_instance = substitute_click_proposition(surface_body, &substitutions).ok()?;
        let proof = plan_finite_instance_proof(
            replay,
            post_state,
            available,
            &instance,
            &surface_instance,
            &values,
            &value_expressions,
            premise_pairs,
        )
        .map(SourceProof::Script)
        .or_else(|| {
            lower_outcome_simp_proof(
                replay,
                &surface_instance,
                &instance,
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
        })?;
        tactics.push(ProofTactic::Have(ProofHave {
            proposition: surface_instance,
            proof,
        }));
    }
    tactics.push(ProofTactic::Enumerate);
    Some(tactics)
}

/// The direct proof of one non-vacuous enumeration instance: introduce its
/// constant guard, then discharge the conclusion from one listed universal
/// premise instantiated at one of the instance's own spelled values. A
/// candidate that would need a transport is accepted only when the same
/// certified-transport judgment the replay runs already connects its
/// instantiated conclusion to the instance goal.
#[allow(clippy::too_many_arguments)]
fn plan_finite_instance_proof(
    replay: &TacticReplayState,
    post_state: &CState,
    available: &[Proposition],
    instance: &Proposition,
    surface_instance: &ClickProposition,
    values: &[i64],
    value_expressions: &[ContractExpression],
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (antecedent, conclusion, surface_conclusion) = match (instance, surface_instance) {
        (
            Proposition::Implies(antecedent, conclusion),
            ClickProposition::Implies(_, surface_conclusion),
        ) => (
            Some(antecedent.as_ref()),
            conclusion.as_ref(),
            surface_conclusion.as_ref(),
        ),
        (instance, surface_instance) => (None, instance, surface_instance),
    };
    let premise_kernels = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let conclusion_gate = |source: &Proposition| -> bool {
        let explicit_assumptions = premise_kernels.iter().cloned().fold(
            assumptions_from_propositions(std::slice::from_ref(source)),
            |assumptions, fact| assumptions.assume_proposition(fact),
        );
        let implicit_assumptions = available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        let transition_facts = fact_transport_transition_facts(&replay.effect_facts, source);
        let transport_assumptions = transition_facts
            .iter()
            .fold(implicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        certified_fact_transport_reaches_through(
            source,
            conclusion,
            post_state.memory(),
            &transport_assumptions,
            &transition_facts,
        )
    };
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        if !matches!(kernel, Proposition::ForAll { .. }) {
            continue;
        }
        let mut discharge_kernels = antecedent.into_iter().cloned().collect::<Vec<_>>();
        let mut using_surfaces = Vec::new();
        for (other, (other_kernel, other_surface)) in premise_pairs.iter().enumerate() {
            if other == index {
                continue;
            }
            discharge_kernels.push(other_kernel.clone());
            using_surfaces.push(other_surface.clone());
        }
        for (value, value_expression) in values.iter().zip(value_expressions) {
            let Ok(argument) = u32::try_from(*value) else {
                continue;
            };
            let Some(mut body_tactics) = plan_explicit_universal_conclusion_discharge(
                kernel,
                surface,
                Bitvector32Term::Constant(argument),
                value_expression,
                conclusion,
                surface_conclusion,
                &discharge_kernels,
                &using_surfaces,
                Some(&conclusion_gate),
            ) else {
                continue;
            };
            let mut tactics = Vec::new();
            if antecedent.is_some() {
                tactics.push(ProofTactic::Intro);
            }
            tactics.append(&mut body_tactics);
            return Some(tactics);
        }
    }
    None
}

fn collect_surface_conjunct_pairs(
    kernel: &Proposition,
    surface: &ClickProposition,
    pairs: &mut Vec<(Proposition, ClickProposition)>,
    extracted: &mut Vec<ClickProposition>,
) {
    let (
        Proposition::And(kernel_left, kernel_right),
        ClickProposition::And(surface_left, surface_right),
    ) = (kernel, surface)
    else {
        return;
    };
    for (kernel_child, surface_child) in [
        (kernel_left.as_ref(), surface_left.as_ref()),
        (kernel_right.as_ref(), surface_right.as_ref()),
    ] {
        if !pairs.iter().any(|(existing, _)| existing == kernel_child) {
            pairs.push((kernel_child.clone(), surface_child.clone()));
            extracted.push(surface_child.clone());
        }
        collect_surface_conjunct_pairs(kernel_child, surface_child, pairs, extracted);
    }
}

fn plan_explicit_increment_lower_bound_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // A named local or post-store field bound can be proved at the latest
    // retained program point and then transported to the requested surface
    // spelling. Keep those two proof steps explicit: the arithmetic theorem
    // does not itself know about stores or snapshot drift, and `transport
    // using` is the simple rule that crosses them.
    // Greater-equal surface goals have their own direct named rule later in
    // certificate planning; preserve that smaller certificate instead of
    // rewriting their orientation through this transport path.
    if matches!(
        surface_goal,
        ClickProposition::Comparison {
            operator: ComparisonOperator::GreaterEqual,
            ..
        }
    ) {
        return None;
    }
    let normalized_goal = normalize_direct_atomic_memory_loads(goal);
    let (goal_lower, _) = signed_nonstrict_parts(&normalized_goal)?;
    let normalized_pairs = premise_pairs
        .iter()
        .map(|(kernel, surface)| {
            (
                normalize_direct_atomic_memory_loads(kernel),
                surface.clone(),
            )
        })
        .collect::<Vec<_>>();
    for (lower_kernel, lower_surface) in &normalized_pairs {
        let Some((lower, base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if lower != goal_lower {
            continue;
        }
        let Some((surface_lower, surface_base)) = surface_nonstrict_parts(lower_surface) else {
            continue;
        };
        for (upper_kernel, upper_surface) in &normalized_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let Some((_, surface_upper)) = surface_strict_parts(upper_surface) else {
                continue;
            };
            let intermediate_surface = ClickProposition::Comparison {
                left: surface_lower.clone(),
                operator: ComparisonOperator::LessEqual,
                right: ContractExpression::Add(
                    Box::new(surface_base.clone()),
                    Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
                ),
            };
            if &intermediate_surface == surface_goal {
                continue;
            }
            return Some(vec![
                ProofTactic::Have(ProofHave {
                    proposition: intermediate_surface.clone(),
                    proof: SourceProof::Script(vec![
                        ProofTactic::ApplyTheoremUsing {
                            application: TheoremApplication {
                                name: "int32_increment_lower_bound".to_string(),
                                arguments: vec![surface_base, surface_lower, surface_upper],
                            },
                            premises: vec![lower_surface.clone(), upper_surface.clone()],
                        },
                        ProofTactic::Assumption,
                    ]),
                }),
                ProofTactic::TransportUsing {
                    source: intermediate_surface.clone(),
                    target: surface_goal.clone(),
                    premises: vec![intermediate_surface],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

#[cfg(test)]
#[test]
fn increment_lower_bound_transport_matches_source_anchored_constant() {
    let selector = VisitSelector::ProgramPoint(ProgramPointRef {
        region: CodeRegionRef::Statement(5),
        kind: ProgramPointKind::Entry,
    });
    let at = |expression| ContractExpression::At {
        selector: selector.clone(),
        expression: Box::new(expression),
    };
    let zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
    let index = ContractExpression::CFragment(CExpression::Variable("index".into()));
    let capacity = ContractExpression::CFragment(CExpression::Variable("capacity".into()));
    let goal = ClickProposition::Comparison {
        left: zero.clone(),
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::CFragment(CExpression::Variable("stored_length".into())),
    };
    let index_term = Bitvector32Term::Variable(Variable(1));
    let capacity_term = Bitvector32Term::Variable(Variable(2));
    let kernel_goal = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(Bitvector32Term::Constant(0)),
            Box::new(Bitvector32Term::Variable(Variable(3))),
        ),
        true,
    );
    let premise_pairs = vec![
        (
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::Constant(0)),
                    Box::new(index_term.clone()),
                ),
                true,
            ),
            ClickProposition::Comparison {
                left: at(zero),
                operator: ComparisonOperator::LessEqual,
                right: at(index),
            },
        ),
        (
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(index_term),
                    Box::new(capacity_term),
                ),
                true,
            ),
            ClickProposition::Comparison {
                left: at(ContractExpression::CFragment(CExpression::Variable(
                    "index".into(),
                ))),
                operator: ComparisonOperator::LessThan,
                right: at(capacity),
            },
        ),
    ];

    assert!(
        plan_explicit_increment_lower_bound_transport(&kernel_goal, &goal, &premise_pairs)
            .is_some(),
        "source-site annotation on the constant must not hide the increment certificate"
    );
}

fn contract_expression_for_instantiation_value(
    value: &Bitvector32Term,
) -> Option<ContractExpression> {
    let Bitvector32Term::Constant(bits) = value else {
        return None;
    };
    Some(ContractExpression::CFragment(CExpression::Value(
        CValue::Int32(Bitvector32Term::Constant(*bits)),
    )))
}

/// Plans an explicit universal-instantiation certificate: one listed
/// universal premise, specialized at an explicit constant, proves the goal
/// after its guards discharge from the remaining listed premises. Emits the
/// named `instantiate ... using` rule and closes by assumption.
fn plan_explicit_forall_instantiation(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let normalized_goal = normalize_direct_atomic_memory_loads(goal);
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let Proposition::ForAll { var, sort, body } = kernel else {
            continue;
        };
        if *sort != Sort::CInt32 {
            continue;
        }
        let other_kernels = premise_pairs
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != index)
            .map(|(_, (kernel, _))| kernel.clone())
            .collect::<Vec<_>>();
        let other_surfaces = premise_pairs
            .iter()
            .enumerate()
            .filter(|(other, _)| *other != index)
            .map(|(_, (_, surface))| surface.clone())
            .collect::<Vec<_>>();
        for value in crate::kernel::forall_instantiation_candidate_values(kernel, goal) {
            let Some(argument) = contract_expression_for_instantiation_value(&value) else {
                continue;
            };
            let instantiated = substitute_int32_variable_in_proposition(body, *var, value.clone());
            let Ok((_, conclusion)) = discharge_instantiated_guards(instantiated, &other_kernels)
            else {
                continue;
            };
            // The closer is `assumption`, so the instantiated conclusion must
            // match the goal by exactly the equivalence assumption replays.
            if conclusion != *goal
                && normalize_direct_atomic_memory_loads(&conclusion) != normalized_goal
            {
                continue;
            }
            let tactics = vec![
                ProofTactic::InstantiateUsing {
                    quantified: surface.clone(),
                    argument,
                    premises: other_surfaces.clone(),
                },
                ProofTactic::Assumption,
            ];
            return Some(tactics);
        }
    }
    None
}

/// Plans an explicit certificate for a universal goal: introduce the binder
/// (and implication antecedent), specialize one listed universal premise at
/// the introduced binder, and close by assumption. The instantiated guards
/// discharge from the introduced antecedent plus the remaining listed
/// premises.
/// One explicit `instantiate ... using` (plus its optional closing transport
/// and `assumption`) that discharges `goal_conclusion` from a universal
/// premise at the given argument. Shared between the binder-introduction
/// forall-goal chain and spelled finite-enumeration instances.
#[allow(clippy::too_many_arguments)]
fn plan_explicit_universal_conclusion_discharge(
    premise_kernel: &Proposition,
    premise_surface: &ClickProposition,
    argument_term: Bitvector32Term,
    argument_expression: &ContractExpression,
    goal_conclusion: &Proposition,
    surface_goal_conclusion: &ClickProposition,
    discharge_kernels: &[Proposition],
    using_surfaces: &[ClickProposition],
    conclusion_gate: Option<&dyn Fn(&Proposition) -> bool>,
) -> Option<Vec<ProofTactic>> {
    let Proposition::ForAll {
        var: premise_var,
        sort: Sort::CInt32,
        body: premise_body,
    } = premise_kernel
    else {
        return None;
    };
    let instantiated =
        substitute_int32_variable_in_proposition(premise_body, *premise_var, argument_term);
    let (_, conclusion) = discharge_instantiated_guards(instantiated, discharge_kernels).ok()?;
    let closes_by_assumption = conclusion == *goal_conclusion
        || normalize_direct_atomic_memory_loads(&conclusion)
            == normalize_direct_atomic_memory_loads(goal_conclusion);
    // Constant-argument instances offer several instantiation candidates, so
    // the caller may insist the instantiated conclusion provably reaches the
    // goal before accepting a transport that replay would reject.
    if !closes_by_assumption
        && let Some(gate) = conclusion_gate
        && !gate(&conclusion)
    {
        return None;
    }
    // A residual spelling difference (for example a loop counter the listed
    // order facts pin to a constant) crosses through an explicit transport
    // from the instantiated conclusion instead. The transported closure is
    // validated by the caller's immediate certificate replay, so no weaker
    // equivalence pre-check runs here.
    let transport_closure = if closes_by_assumption {
        None
    } else {
        // A loop-exit universal invariant fact is spelled through an
        // `at(point, ...)` wrapper; peel it here and restore it on the
        // substituted transport source so the source lowers at the same
        // snapshot the premise denotes.
        let (premise_selector, premise_forall) = match premise_surface {
            ClickProposition::At {
                selector,
                proposition,
            } => (Some(selector), proposition.as_ref()),
            other => (None, other),
        };
        let ClickProposition::ForAll {
            name: premise_binder,
            body: premise_surface_body,
            ..
        } = premise_forall
        else {
            return None;
        };
        let premise_surface_conclusion = match premise_surface_body.as_ref() {
            ClickProposition::Implies(_, conclusion) => conclusion.as_ref(),
            body => body,
        };
        let substitutions = std::iter::once((premise_binder.clone(), argument_expression.clone()))
            .collect::<BTreeMap<_, _>>();
        let source =
            substitute_click_proposition(premise_surface_conclusion, &substitutions).ok()?;
        let source = match premise_selector {
            Some(selector) => ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(source),
            },
            None => source,
        };
        Some((source, surface_goal_conclusion.clone()))
    };
    let mut tactics = vec![ProofTactic::InstantiateUsing {
        quantified: premise_surface.clone(),
        argument: argument_expression.clone(),
        premises: using_surfaces.to_vec(),
    }];
    if let Some((source, target)) = transport_closure {
        let mut transport_premises = vec![source.clone()];
        transport_premises.extend(using_surfaces.iter().cloned());
        tactics.push(ProofTactic::TransportUsing {
            source,
            target,
            premises: transport_premises,
        });
    }
    tactics.push(ProofTactic::Assumption);
    Some(tactics)
}

fn plan_explicit_forall_goal(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    effect_facts: &[ExecutionPureFact],
    post_state: &CState,
) -> Option<Vec<ProofTactic>> {
    let Proposition::ForAll {
        var: goal_var,
        sort: Sort::CInt32,
        body: goal_body,
    } = goal
    else {
        return None;
    };
    let ClickProposition::ForAll {
        name: binder_name,
        body: surface_body,
        ..
    } = surface_goal
    else {
        return None;
    };
    let (antecedent, goal_conclusion, surface_antecedent) =
        match (goal_body.as_ref(), surface_body.as_ref()) {
            (
                Proposition::Implies(antecedent, conclusion),
                ClickProposition::Implies(surface_antecedent, _),
            ) => (
                Some(antecedent.as_ref().clone()),
                conclusion.as_ref(),
                Some(surface_antecedent.as_ref().clone()),
            ),
            (body, _) => (None, body, None),
        };
    let surface_goal_conclusion = match surface_body.as_ref() {
        ClickProposition::Implies(_, conclusion) => conclusion.as_ref(),
        body => body,
    };
    for (index, (kernel, surface)) in premise_pairs.iter().enumerate() {
        let mut discharge_kernels = antecedent.iter().cloned().collect::<Vec<_>>();
        let mut using_surfaces = surface_antecedent.iter().cloned().collect::<Vec<_>>();
        for (other, (other_kernel, other_surface)) in premise_pairs.iter().enumerate() {
            if other == index {
                continue;
            }
            discharge_kernels.push(other_kernel.clone());
            using_surfaces.push(other_surface.clone());
        }
        let Some(mut body_tactics) = plan_explicit_universal_conclusion_discharge(
            kernel,
            surface,
            Bitvector32Term::Variable(*goal_var),
            &ContractExpression::CFragment(CExpression::Variable(binder_name.clone())),
            goal_conclusion,
            surface_goal_conclusion,
            &discharge_kernels,
            &using_surfaces,
            None,
        ) else {
            continue;
        };
        let mut tactics = vec![ProofTactic::Intro];
        if antecedent.is_some() {
            tactics.push(ProofTactic::Intro);
        }
        tactics.append(&mut body_tactics);
        return Some(tactics);
    }
    // Without a universal premise the body may still be a preserved load:
    // discharge it point-wise with the explicit unchanged-load transport
    // under the same binder introduction.
    let surface_conclusion = match surface_body.as_ref() {
        ClickProposition::Implies(_, conclusion) => conclusion.as_ref(),
        body => body,
    };
    let introduced = antecedent.iter().cloned().collect::<Vec<_>>();
    let mut body_tactics = plan_explicit_unchanged_load_transport(
        goal_conclusion,
        surface_conclusion,
        premise_pairs,
        available,
        effect_facts,
        post_state,
        &introduced,
    )?;
    // The introduced bounds are what place the binder's cell inside the
    // preserved range, so the point-wise transport must name them. A simple
    // transport consumes atomic premises; spell conjunction elimination
    // explicitly after introducing the guarded antecedent.
    let mut extracted = Vec::new();
    if let Some(antecedent_surface) = &surface_antecedent {
        for tactic in &mut body_tactics {
            if let ProofTactic::TransportUsing { premises, .. } = tactic {
                premises.push(antecedent_surface.clone());
                let original = std::mem::take(premises);
                for premise in original {
                    flatten_transport_premise(&premise, &mut extracted, premises);
                }
            }
        }
    }
    let mut tactics = vec![ProofTactic::Intro];
    if antecedent.is_some() {
        tactics.push(ProofTactic::Intro);
    }
    tactics.extend(extracted.into_iter().map(ProofTactic::Extract));
    tactics.append(&mut body_tactics);
    Some(tactics)
}

fn plan_explicit_unchanged_load_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    effect_facts: &[ExecutionPureFact],
    post_state: &CState,
    introduced: &[Proposition],
) -> Option<Vec<ProofTactic>> {
    let ClickProposition::Comparison {
        operator: ComparisonOperator::Equal,
        right,
        ..
    } = surface_goal
    else {
        return None;
    };
    if !contains_old_expression(right) {
        return None;
    }
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, kernel_right), kernel_value) =
        goal
    else {
        return None;
    };
    let source_kernel = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(kernel_right.clone(), kernel_right.clone()),
        *kernel_value,
    );
    let mut selected = Vec::<(Proposition, ClickProposition)>::new();
    let replays = |selected: &[(Proposition, ClickProposition)]| {
        let explicit = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .chain(introduced.iter().cloned())
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
        if selected_assumptions
            .derive_atomic_proposition(&source_kernel)
            .is_none()
        {
            return false;
        }
        let transition_facts = fact_transport_transition_facts(effect_facts, &source_kernel);
        let transport_assumptions = transition_facts
            .iter()
            .fold(selected_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source_kernel.clone());
        certified_fact_transport_reaches_through(
            &source_kernel,
            goal,
            post_state.memory(),
            &transport_assumptions,
            &transition_facts,
        )
    };
    if !replays(&selected) {
        let rank = |proposition: &Proposition| match proposition {
            Proposition::CResourceSeparate { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. } => 0,
            Proposition::ConditionIs(_, _) => 1,
            _ => 2,
        };
        let mut candidates = premise_pairs.to_vec();
        candidates.sort_by_key(|(kernel, _)| rank(kernel));
        for candidate in candidates {
            if selected.contains(&candidate) {
                continue;
            }
            selected.push(candidate);
            if replays(&selected) {
                break;
            }
        }
    }
    if !replays(&selected) {
        return None;
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
    let premises = selected.into_iter().map(|(_, surface)| surface).collect();
    let source = ClickProposition::Comparison {
        left: right.clone(),
        operator: ComparisonOperator::Equal,
        right: right.clone(),
    };
    // The reflexive source normalizes context-free; the transport replay
    // materializes its symbolic load spelling itself, so no nested `have` is
    // needed (a nested proof could not see an introduced universal binder).
    Some(vec![
        ProofTactic::TransportUsing {
            source,
            target: surface_goal.clone(),
            premises,
        },
        ProofTactic::Assumption,
    ])
}

pub(super) fn lower_restricted_simp_plan(
    goal: &Proposition,
    surface_goal: Option<&ClickProposition>,
    plan: &SimpEvidence,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Result<Vec<ProofTactic>, ClickError> {
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let assumptions = assumptions_from_propositions(&available);
    let exact_derivation = match plan {
        SimpEvidence::Assumption => {
            if !pure_fact_is_replay_available(goal, &available) {
                return Err(ClickError::new(
                    "`simp() using` selected `assumption`, but the goal is not one of its listed premises",
                ));
            }
            None
        }
        SimpEvidence::Normalize => {
            if !normalizes_context_free(goal) {
                return Err(ClickError::new(
                    "`simp() using` selected `normalize`, but the goal is not context-free",
                ));
            }
            None
        }
        SimpEvidence::Derivation(derivation) => {
            if derivation.conclusion() != goal || !derivation.replay(&assumptions) {
                return Err(ClickError::new(
                    "`simp() using` selected a derivation that does not replay from exactly its listed premises",
                ));
            }
            Some(derivation)
        }
    };

    if let Some((choose_left, child)) =
        exact_derivation.and_then(|proof| proof.disjunction_choice())
    {
        let Proposition::Or(left, right) = goal else {
            return Err(ClickError::new(
                "`simp() using` selected a disjunction proof for a non-disjunction goal",
            ));
        };
        let child_goal = if choose_left {
            left.as_ref()
        } else {
            right.as_ref()
        };
        // `left`/`right` replay accepts the selected disjunct when it is the
        // same total boolean condition as an available fact up to polarity
        // (e.g. `x > 0` from `not (x <= 0)`); construction mirrors exactly
        // that check rather than demanding the literal spelling.
        let disjunct_replays = pure_fact_is_replay_available(child_goal, &available)
            || available
                .iter()
                .any(|fact| condition_polarity_equivalent(fact, child_goal));
        if child.conclusion() != child_goal || !disjunct_replays {
            return Err(ClickError::new(
                "`simp() using` selected a derived disjunct that needs an explicit intermediate `have`",
            ));
        }
        return Ok(vec![if choose_left {
            ProofTactic::Left
        } else {
            ProofTactic::Right
        }]);
    }

    let named_rule = |goal: &Proposition| plan_explicit_named_signed_rule(goal, premise_pairs);
    let loadability_transport = || {
        exact_derivation?;
        plan_explicit_loadability_transport(goal, surface_goal?, premise_pairs)
    };
    let tactics = loadability_transport()
        .or_else(|| named_rule(goal))
        .or_else(|| {
            plan_explicit_equality_rewrites_then(
                goal,
                premise_pairs,
                &available,
                &named_rule,
            )
        })
        .ok_or_else(|| {
        let initial_rewrites = premise_pairs
            .iter()
            .map(|(kernel, surface)| {
                let outcome = rewrite_proposition_by_exact_equality(goal, kernel, &available)
                    .map(|_| "applies to the initial goal".to_string())
                    .unwrap_or_else(|error| error);
                format!("{}: {outcome}", describe_click_proposition(surface))
            })
            .collect::<Vec<_>>()
            .join("\n    ");
        ClickError::new(format!(
            "`simp() using` proved the goal, but Click has no explicit simple proof rule for the selected derivation\n  goal: {}\n  listed premises: {}\n    {initial_rewrites}",
            describe_pure_fact(goal, &[], &[]),
            premise_pairs.len(),
        ))
        })?;
    ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
        ClickError::new(format!(
            "`simp() using` produced a non-simple expansion: {error:?}"
        ))
    })?;
    Ok(tactics)
}

pub(super) fn plan_explicit_named_signed_rule(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    plan_explicit_implies_refuted_antecedent(goal, premise_pairs)
        .or_else(|| plan_explicit_discharged_implication_consequent(goal, premise_pairs))
        .or_else(|| plan_explicit_one_plus_strictly_increases(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_strictly_increases(goal, premise_pairs))
        .or_else(|| plan_explicit_successor_le_implies_lt(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_preserves_order(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_lower_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_upper_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_positive_is_nonnegative(goal, premise_pairs))
        .or_else(|| plan_explicit_le_transitive_constant_lower(goal, premise_pairs))
        .or_else(|| plan_explicit_strictly_positive_is_nonnegative(goal, premise_pairs))
        .or_else(|| plan_explicit_strict_implies_nonstrict(goal, premise_pairs))
        .or_else(|| plan_explicit_greater_equal_to_reversed_less_equal(goal, premise_pairs))
        .or_else(|| plan_explicit_not_strict_implies_greater_equal(goal, premise_pairs))
        .or_else(|| plan_explicit_greater_equal_transitive(goal, premise_pairs))
        .or_else(|| plan_explicit_negated_strict_successor_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_greater_equal_lower_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_strict_greater_lower_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_strict_transitive(goal, premise_pairs))
        .or_else(|| plan_explicit_nonstrict_then_strict_transitive(goal, premise_pairs))
        .or_else(|| plan_explicit_strict_then_nonstrict_transitive(goal, premise_pairs))
        .or_else(|| plan_explicit_constant_lower_bound_weakening(goal, premise_pairs))
        .or_else(|| plan_explicit_constant_strict_upper_bound_weakening(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_constant_upper_bound(goal, premise_pairs))
        .or_else(|| plan_explicit_increment_below_max_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_one_plus_below_max_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_nonnegative_add_within_max_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_nonnegative_subtract_within_value_is_defined(goal, premise_pairs))
        .or_else(|| plan_explicit_positive_predecessor_is_nonnegative(goal, premise_pairs))
        .or_else(|| plan_explicit_predecessor_upper_bound(goal, premise_pairs, false))
        .or_else(|| plan_explicit_one_le_predecessor(goal, premise_pairs))
        .or_else(|| plan_explicit_positive_predecessor_strictly_decreases(goal, premise_pairs))
        .or_else(|| plan_explicit_le_and_neq_implies_lt(goal, premise_pairs))
        .or_else(|| plan_explicit_le_and_not_lt_implies_eq(goal, premise_pairs))
        .or_else(|| plan_explicit_ge_and_not_gt_implies_eq(goal, premise_pairs))
}

fn plan_explicit_le_and_neq_implies_lt(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (left, right) = goal_exact_less_than_parts(goal)?;
    for (le_kernel, le_surface) in premise_pairs {
        let Some((le_left, le_right)) = signed_nonstrict_parts(le_kernel) else {
            continue;
        };
        if le_left != left || le_right != right {
            continue;
        }
        for (neq_kernel, neq_surface) in premise_pairs {
            let matches_neq = match neq_kernel {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(neq_left, neq_right),
                    false,
                ) => neq_left.as_ref() == left && neq_right.as_ref() == right,
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(neq_left, neq_right),
                        true,
                    ) if neq_left.as_ref() == left && neq_right.as_ref() == right
                ),
                _ => false,
            };
            if !matches_neq {
                continue;
            }
            let (surface_left, surface_right) = surface_nonstrict_parts(le_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_le_and_neq_implies_lt".to_string(),
                        arguments: vec![surface_left, surface_right],
                    },
                    premises: vec![le_surface.clone(), neq_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_loadability_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    if !matches!(goal, Proposition::CMemoryLoadable { .. }) {
        return None;
    }
    let Proposition::CMemoryLoadable {
        bytes: goal_bytes, ..
    } = goal
    else {
        unreachable!()
    };
    let mut sources = premise_pairs
        .iter()
        .filter(|(kernel, _)| matches!(kernel, Proposition::CMemoryLoadable { .. }))
        .collect::<Vec<_>>();
    let surface_is_range = |surface: &ClickProposition| match surface {
        ClickProposition::At { proposition, .. } => {
            matches!(
                proposition.as_ref(),
                ClickProposition::Loadable { segment }
                    if matches!(segment.surface, ContractSegmentSurface::Range { .. })
            )
        }
        ClickProposition::Loadable { segment } => {
            matches!(segment.surface, ContractSegmentSurface::Range { .. })
        }
        _ => false,
    };
    sources.sort_by_key(|(kernel, surface)| match kernel {
        Proposition::CMemoryLoadable { bytes, .. } => (
            (!surface_is_range(surface)) as u8,
            (bytes == goal_bytes) as u8,
        ),
        _ => unreachable!(),
    });
    for (source, surface_source) in sources {
        let mut selected = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::CMemoryLoadable { .. } | Proposition::ConditionIs(_, _)
                )
            })
            .collect::<Vec<_>>();
        let proves_goal = |pairs: &[&(Proposition, ClickProposition)]| {
            let propositions = pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            assumptions_from_propositions(&propositions)
                .derive_simp_proposition(goal)
                .is_some()
        };
        if !proves_goal(&selected) {
            continue;
        }
        let mut index = 0;
        while index < selected.len() {
            if selected[index].0 == *source {
                index += 1;
                continue;
            }
            let mut reduced = selected.clone();
            reduced.remove(index);
            if proves_goal(&reduced) {
                selected = reduced;
            } else {
                index += 1;
            }
        }
        let selected_kernel = selected
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        debug_assert!(
            assumptions_from_propositions(&selected_kernel)
                .derive_simp_proposition(goal)
                .is_some()
        );
        return Some(vec![
            ProofTactic::TransportUsing {
                source: surface_source.clone(),
                target: surface_goal.clone(),
                premises: selected
                    .into_iter()
                    .map(|(_, surface)| surface.clone())
                    .collect(),
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn signed_strict_parts(proposition: &Proposition) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left, right))
        }
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(left, right),
            true,
        ) => Some((right, left)),
        _ => None,
    }
}

pub(super) fn signed_nonstrict_parts(
    proposition: &Proposition,
) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left, right))
        }
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
            true,
        ) => Some((right, left)),
        _ => None,
    }
}

/// Transcribe one kernel-selected signed-order path. Each intermediate edge
/// is established with the matching named transitivity theorem and retained
/// as a nested `have`; the final two-edge suffix uses the ordinary exact
/// named-rule translator so the original goal orientation is preserved.
pub(super) fn recorded_signed_order_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation.signed_order_path().and_then(|path| {
        path.iter()
            .map(|step| {
                premise_pairs
                    .iter()
                    .find(|(kernel, _)| kernel == step.premise())
            })
            .collect::<Option<Vec<_>>>()
            .map(|pairs| pairs.into_iter().cloned().collect::<Vec<_>>())
    })
}

pub(super) fn recorded_int32_increment_upper_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation.int32_increment_upper_bound_step()?.premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_increment_constant_upper_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_increment_constant_upper_bound_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_increment_strictly_increases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_increment_strictly_increases_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_increment_below_max_is_defined_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_increment_below_max_is_defined_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_one_plus_below_max_is_defined_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_one_plus_below_max_is_defined_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_one_plus_strictly_increases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_one_plus_strictly_increases_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_nonnegative_add_within_max_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (amount_nonnegative, within_headroom) =
        derivation.int32_nonnegative_add_within_max_steps()?;
    [amount_nonnegative.premise(), within_headroom.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_nonnegative_subtract_within_value_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (amount_nonnegative, within_value) =
        derivation.int32_nonnegative_subtract_within_value_steps()?;
    [amount_nonnegative.premise(), within_value.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_increment_lower_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (lower_bound, upper_bound) = derivation.int32_increment_lower_bound_steps()?;
    [lower_bound.premise(), upper_bound.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_increment_greater_equal_lower_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (lower_bound, upper_bound) =
        derivation.int32_increment_greater_equal_lower_bound_steps()?;
    [lower_bound.premise(), upper_bound.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_increment_strict_greater_lower_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (lower_bound, upper_bound) =
        derivation.int32_increment_strict_greater_lower_bound_steps()?;
    [lower_bound.premise(), upper_bound.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_increment_strict_greater_from_strict_lower_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (lower_bound, upper_bound) =
        derivation.int32_increment_strict_greater_from_strict_lower_steps()?;
    [lower_bound.premise(), upper_bound.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_increment_preserves_order_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (lower_bound, upper_bound) = derivation.int32_increment_preserves_order_steps()?;
    [lower_bound.premise(), upper_bound.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_positive_predecessor_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_positive_predecessor_is_nonnegative_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_positive_predecessor_strictly_decreases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_positive_predecessor_strictly_decreases_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_nonnegative_predecessor_upper_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (nonnegative, upper_bound) =
        derivation.int32_nonnegative_predecessor_upper_bound_steps()?;
    [nonnegative.premise(), upper_bound.premise()]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == premise)
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_one_le_predecessor_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_one_le_predecessor_is_nonnegative_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_one_le_predecessor_strictly_decreases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_one_le_predecessor_strictly_decreases_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_le_and_not_lt_implies_equality_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (less_equal, not_less_than) = derivation.int32_le_and_not_lt_implies_equality_premises()?;
    [less_equal, not_less_than]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| {
                    kernel == premise || condition_polarity_equivalent(kernel, premise)
                })
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_ge_and_not_gt_implies_equality_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (greater_equal, not_greater_than) =
        derivation.int32_ge_and_not_gt_implies_equality_premises()?;
    [greater_equal, not_greater_than]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| {
                    kernel == premise || condition_polarity_equivalent(kernel, premise)
                })
                .cloned()
        })
        .collect()
}

pub(super) fn recorded_int32_positive_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation.int32_positive_is_nonnegative_step()?.premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_strictly_positive_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_strictly_positive_is_nonnegative_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_successor_le_implies_lt_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation.int32_successor_le_implies_lt_step()?.premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_constant_lower_bound_weakening_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_constant_lower_bound_weakening_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise)
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_negated_strict_successor_bound_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let premise = derivation
        .int32_negated_strict_successor_bound_step()?
        .premise();
    premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == premise || condition_polarity_equivalent(kernel, premise))
        .cloned()
        .map(|pair| vec![pair])
}

pub(super) fn recorded_int32_le_and_neq_implies_strict_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    let (less_equal, not_equal) = derivation.int32_le_and_neq_implies_strict_premises()?;
    [less_equal, not_equal]
        .into_iter()
        .map(|premise| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| {
                    kernel == premise || condition_polarity_equivalent(kernel, premise)
                })
                .cloned()
        })
        .collect()
}

pub(super) fn plan_recorded_int32_increment_upper_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_upper_bound(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_constant_upper_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_constant_upper_bound(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_strictly_increases_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_strictly_increases(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_below_max_is_defined_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_below_max_is_defined(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_one_plus_below_max_is_defined_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_one_plus_below_max_is_defined(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_one_plus_strictly_increases_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_one_plus_strictly_increases(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_nonnegative_add_within_max_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_nonnegative_add_within_max_is_defined(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_nonnegative_subtract_within_value_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics =
        plan_explicit_nonnegative_subtract_within_value_is_defined(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_lower_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_lower_bound(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_greater_equal_lower_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_greater_equal_lower_bound(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_strict_greater_lower_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_strict_greater_lower_bound(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_strict_greater_from_strict_lower_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics =
        plan_explicit_increment_strict_greater_from_strict_lower(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_increment_preserves_order_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_increment_preserves_order(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_positive_predecessor_is_nonnegative_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_positive_predecessor_is_nonnegative(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_positive_predecessor_strictly_decreases_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_positive_predecessor_strictly_decreases(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_predecessor_upper_bound(goal, premise_pairs, false)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_one_le_predecessor_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_one_le_predecessor(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
        let ProofTactic::Have(have) = tactics.first_mut()? else {
            return None;
        };
        let SourceProof::Script(body) = &mut have.proof else {
            return None;
        };
        remove_trailing_theorem_assumption(body)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_le_and_not_lt_implies_eq(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_ge_and_not_gt_implies_equality_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_ge_and_not_gt_implies_eq(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_positive_is_nonnegative_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_positive_is_nonnegative(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_strictly_positive_is_nonnegative_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_strictly_positive_is_nonnegative(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_successor_le_implies_lt_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_successor_le_implies_lt(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_constant_lower_bound_weakening_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_le_transitive_constant_lower(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_negated_strict_successor_bound_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_negated_strict_successor_bound(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
        let ProofTactic::Have(have) = tactics.first_mut()? else {
            return None;
        };
        let SourceProof::Script(body) = &mut have.proof else {
            return None;
        };
        remove_trailing_theorem_assumption(body)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_int32_le_and_neq_implies_strict_for_context(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let mut tactics = plan_explicit_le_and_neq_implies_lt(goal, premise_pairs)?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut tactics)?;
    }
    Some(tactics)
}

pub(super) fn plan_recorded_signed_order_path(
    goal: &Proposition,
    path: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    plan_recorded_signed_order_path_for_context(goal, path, false)
}

/// Point theorem applications complete an exact matching proposition goal,
/// while pure theorem applications add their conclusion and leave the goal
/// for `assumption`. Keep that semantic distinction in the path planner so
/// the checked point successor never contains a redundant, invalid closer.
pub(super) fn plan_recorded_signed_order_path_for_context(
    goal: &Proposition,
    path: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    if path.len() < 2 {
        let mut tactics = plan_explicit_named_signed_rule(goal, path)?;
        if point_application_closes_goal {
            remove_trailing_theorem_assumption(&mut tactics)?;
        }
        return Some(tactics);
    }
    let mut tactics = Vec::new();
    let mut current = path[0].clone();
    for next in &path[1..path.len() - 1] {
        let (current_lower, current_upper, current_strict) =
            if let Some((lower, upper)) = signed_strict_parts(&current.0) {
                (lower.clone(), upper.clone(), true)
            } else {
                let (lower, upper) = signed_nonstrict_parts(&current.0)?;
                (lower.clone(), upper.clone(), false)
            };
        let (next_lower, next_upper, next_strict) =
            if let Some((lower, upper)) = signed_strict_parts(&next.0) {
                (lower.clone(), upper.clone(), true)
            } else {
                let (lower, upper) = signed_nonstrict_parts(&next.0)?;
                (lower.clone(), upper.clone(), false)
            };
        if current_upper != next_lower {
            return None;
        }
        let (surface_lower, surface_middle) = if current_strict {
            surface_strict_parts(&current.1)?
        } else {
            surface_nonstrict_parts(&current.1)?
        };
        let (_, surface_upper) = if next_strict {
            surface_strict_parts(&next.1)?
        } else {
            surface_nonstrict_parts(&next.1)?
        };
        let strict = current_strict || next_strict;
        let theorem = match (current_strict, next_strict) {
            (false, false) => "int32_le_transitive",
            (false, true) => "int32_le_lt_transitive",
            (true, false) => "int32_lt_le_transitive",
            (true, true) => "int32_lt_transitive",
        };
        let surface_target = ClickProposition::Comparison {
            left: surface_lower.clone(),
            operator: if strict {
                ComparisonOperator::LessThan
            } else {
                ComparisonOperator::LessEqual
            },
            right: surface_upper.clone(),
        };
        let kernel_target = Proposition::ConditionIs(
            if strict {
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(current_lower),
                    Box::new(next_upper),
                )
            } else {
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(current_lower),
                    Box::new(next_upper),
                )
            },
            true,
        );
        let mut proof = vec![ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: theorem.to_string(),
                arguments: vec![surface_lower, surface_middle, surface_upper],
            },
            premises: vec![current.1.clone(), next.1.clone()],
        }];
        if !point_application_closes_goal {
            proof.push(ProofTactic::Assumption);
        }
        tactics.push(ProofTactic::Have(ProofHave {
            proposition: surface_target.clone(),
            proof: SourceProof::Script(proof),
        }));
        current = (kernel_target, surface_target);
    }
    let final_edge = path.last()?.clone();
    let mut suffix = plan_explicit_named_signed_rule(goal, &[current, final_edge])?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut suffix)?;
    }
    tactics.extend(suffix);
    Some(tactics)
}

fn remove_trailing_theorem_assumption(tactics: &mut Vec<ProofTactic>) -> Option<()> {
    if !matches!(tactics.last(), Some(ProofTactic::Assumption))
        || !matches!(
            tactics.get(tactics.len().checked_sub(2)?),
            Some(ProofTactic::ApplyTheoremUsing { .. })
        )
    {
        return None;
    }
    tactics.pop();
    Some(())
}

fn orient_surface_bitvector_equality(
    step: &BitvectorEqualityDerivationStep,
    surface: &ClickProposition,
) -> Option<ClickProposition> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(premise_left, premise_right),
        true,
    ) = step.premise()
    else {
        return None;
    };
    let reverse = step.source() == premise_right.as_ref() && step.target() == premise_left.as_ref();
    if !reverse
        && !(step.source() == premise_left.as_ref() && step.target() == premise_right.as_ref())
    {
        return None;
    }
    fn oriented(surface: &ClickProposition, reverse: bool) -> Option<ClickProposition> {
        match surface {
            ClickProposition::At {
                selector,
                proposition,
            } => Some(ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(oriented(proposition, reverse)?),
            }),
            ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } => Some(ClickProposition::Comparison {
                left: if reverse { right.clone() } else { left.clone() },
                operator: ComparisonOperator::Equal,
                right: if reverse { left.clone() } else { right.clone() },
            }),
            _ => None,
        }
    }
    oriented(surface, reverse)
}

fn recorded_bitvector_equality_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation.bitvector_equality_path().and_then(|path| {
        path.iter()
            .map(|step| {
                premise_pairs
                    .iter()
                    .find(|(kernel, _)| kernel == step.premise())
                    .cloned()
            })
            .collect()
    })
}

/// Transcribe the exact equality path retained by the kernel. Each edge is
/// oriented in the direction selected by the path, even when its source
/// premise was written in reverse. Rewriting the goal along every edge must
/// end in a context-free reflexive proposition.
pub(super) fn plan_recorded_bitvector_equality_path(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let path = derivation.bitvector_equality_path()?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = goal.clone();
    let mut tactics = Vec::with_capacity(path.len() + 1);
    for step in path {
        let (_, surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == step.premise())?;
        let oriented_surface = orient_surface_bitvector_equality(step, surface)?;
        let oriented_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(step.source().clone()),
                Box::new(step.target().clone()),
            ),
            true,
        );
        current =
            rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available).ok()?;
        tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    if !normalizes_context_free(&current) {
        return None;
    }
    tactics.push(ProofTactic::Normalize);
    Some(tactics)
}

/// The goal-side counterpart of [`signed_strict_parts`]. A named-rule
/// certificate closes with `assumption` against the applied theorem's exact
/// conclusion, so a rule whose theorem concludes `<` may only fire when the
/// goal is spelled `<`; a reversed (`>`) goal needs the reversed-form rule.
fn goal_exact_less_than_parts(goal: &Proposition) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match goal {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left, right))
        }
        _ => None,
    }
}

/// The goal-side counterpart of [`signed_nonstrict_parts`]; see
/// [`goal_exact_less_than_parts`].
fn goal_exact_less_equal_parts(goal: &Proposition) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match goal {
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left, right))
        }
        _ => None,
    }
}

/// Exact `>=`-shaped goal parts as `(lower, value)`; see
/// [`goal_exact_less_than_parts`]. For a theorem whose conclusion is spelled
/// with `>=` (for example `int32_strictly_positive_is_nonnegative`).
fn goal_exact_greater_equal_parts(
    goal: &Proposition,
) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
    match goal {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(value, lower),
            true,
        ) => Some((lower, value)),
        _ => None,
    }
}

fn increment_base(term: &Bitvector32Term) -> Option<&Bitvector32Term> {
    let Bitvector32Term::Add(left, right) = term else {
        return None;
    };
    if right.as_ref() == &Bitvector32Term::Constant(1) {
        Some(left)
    } else if left.as_ref() == &Bitvector32Term::Constant(1) {
        Some(right)
    } else {
        None
    }
}

fn surface_strict_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    if let ClickProposition::At {
        selector,
        proposition,
    } = proposition
    {
        let (left, right) = surface_strict_parts(proposition)?;
        let at = |expression| ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression),
        };
        return Some((at(left), at(right)));
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    match operator {
        ComparisonOperator::LessThan => Some((left.clone(), right.clone())),
        ComparisonOperator::GreaterThan => Some((right.clone(), left.clone())),
        _ => None,
    }
}

pub(super) fn surface_nonstrict_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    if let ClickProposition::At {
        selector,
        proposition,
    } = proposition
    {
        let (left, right) = surface_nonstrict_parts(proposition)?;
        let at = |expression| ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(expression),
        };
        return Some((at(left), at(right)));
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    match operator {
        ComparisonOperator::LessEqual => Some((left.clone(), right.clone())),
        ComparisonOperator::GreaterEqual => Some((right.clone(), left.clone())),
        _ => None,
    }
}

fn plan_explicit_increment_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (incremented, goal_upper) = goal_exact_less_equal_parts(goal)?;
    let base = increment_base(incremented)?;

    for (kernel, surface) in premise_pairs {
        let Some((premise_base, premise_upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_base != base || premise_upper != goal_upper {
            continue;
        }
        let (value, upper) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_upper_bound".to_string(),
                    arguments: vec![value, upper],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_positive_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, goal_value) = goal_exact_less_equal_parts(goal)?;
    if goal_lower != &Bitvector32Term::Constant(0) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(1) || premise_value != goal_value {
            continue;
        }
        let (_, surface_value) = surface_nonstrict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_positive_is_nonnegative".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_le_transitive_constant_lower(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(goal_lower, goal_value),
        true,
    ) = goal
    else {
        return None;
    };
    let Bitvector32Term::Constant(goal_lower_bits) = goal_lower.as_ref() else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        let Bitvector32Term::Constant(premise_lower_bits) = premise_lower else {
            continue;
        };
        if premise_value != goal_value.as_ref()
            || (*goal_lower_bits as i32) >= (*premise_lower_bits as i32)
        {
            continue;
        }
        let constant_leg = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(goal_lower.as_ref().clone()),
                Box::new(premise_lower.clone()),
            ),
            true,
        );
        if !normalizes_context_free(&constant_leg) {
            continue;
        }
        let (surface_middle, surface_value) = surface_nonstrict_parts(surface)?;
        let surface_lower =
            ContractExpression::CFragment(CExpression::Value(int32(*goal_lower_bits)));
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_le_transitive".to_string(),
                    arguments: vec![surface_lower, surface_middle, surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_strict_implies_nonstrict(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let reversed = matches!(
        goal,
        Proposition::ConditionIs(ConditionTerm::Bitvector32SignedGreaterEqual(_, _), true,)
    );
    let (goal_left, goal_right) = signed_nonstrict_parts(goal)?;
    for (kernel, surface) in premise_pairs {
        let Some((premise_left, premise_right)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_left != goal_left || premise_right != goal_right {
            continue;
        }
        let (surface_left, surface_right) = surface_strict_parts(surface)?;
        let surface_nonstrict = ClickProposition::Comparison {
            left: surface_left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: surface_right.clone(),
        };
        let mut tactics = vec![ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_lt_implies_le".to_string(),
                arguments: vec![surface_left.clone(), surface_right.clone()],
            },
            premises: vec![surface.clone()],
        }];
        if reversed {
            tactics.push(ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_le_implies_reversed_ge".to_string(),
                    arguments: vec![surface_left, surface_right],
                },
                premises: vec![surface_nonstrict],
            });
        }
        tactics.push(ProofTactic::Assumption);
        return Some(tactics);
    }
    None
}

/// Plans a vacuous-implication certificate: an implication chain whose
/// antecedent at some depth is refuted by a listed premise closes by
/// introducing antecedents down to the refuted one, then naming the
/// contradiction. Replay pushes each introduced antecedent exactly as the
/// goal spells it, so the refuting premise must be that spelling's exact
/// opposite (flipped condition polarity or a stripped `not`); anything looser
/// would not survive the `contradiction` tactic's exact-match check.
fn plan_explicit_implies_refuted_antecedent(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let mut tactics = Vec::new();
    let mut current = goal;
    while let Proposition::Implies(antecedent, consequent) = current {
        tactics.push(ProofTactic::Intro);
        let refutation = premise_pairs
            .iter()
            .find(|(kernel, _)| match antecedent.as_ref() {
                Proposition::ConditionIs(condition, expected) => {
                    kernel == &Proposition::ConditionIs(condition.clone(), !expected)
                }
                Proposition::Not(inner) => kernel == inner.as_ref(),
                _ => false,
            });
        if let Some((_, surface)) = refutation {
            tactics.push(ProofTactic::Contradiction(surface.clone()));
            return Some(tactics);
        }
        current = consequent;
    }
    None
}

/// Modus ponens over a listed implication premise: walk a (possibly chained)
/// implication whose antecedents are each listed premises, and close the goal
/// when a consequent along the walk is the goal. The emitted `extract` names
/// the consequent's surface spelling, so replay re-checks the same bounded
/// rule; `assumption` then closes the goal from the extracted fact.
fn plan_explicit_discharged_implication_consequent(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let antecedent_listed = |antecedent: &Proposition| {
        premise_pairs.iter().any(|(kernel, _)| {
            kernel == antecedent || condition_polarity_equivalent(kernel, antecedent)
        })
    };
    for (kernel, surface) in premise_pairs {
        let mut current = (kernel, surface);
        while let (
            Proposition::Implies(antecedent, consequent),
            ClickProposition::Implies(_, surface_consequent),
        ) = (current.0, current.1)
        {
            if !antecedent_listed(antecedent) {
                break;
            }
            if consequent.as_ref() == goal || condition_polarity_equivalent(consequent, goal) {
                return Some(vec![
                    ProofTactic::Extract(surface_consequent.as_ref().clone()),
                    ProofTactic::Assumption,
                ]);
            }
            current = (consequent, surface_consequent);
        }
    }
    None
}

fn plan_explicit_greater_equal_to_reversed_less_equal(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(goal_lower, goal_greater),
        true,
    ) = goal
    else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(greater, lower),
            true,
        ) = kernel
        else {
            continue;
        };
        if greater != goal_greater || lower != goal_lower {
            continue;
        }
        let (surface_lower, surface_greater) = surface_nonstrict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_ge_implies_reversed_le".to_string(),
                    arguments: vec![surface_greater, surface_lower],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_not_strict_implies_greater_equal(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(goal_left, goal_right),
        true,
    ) = goal
    else {
        return None;
    };
    for (kernel, surface) in premise_pairs {
        let matches = match kernel {
            Proposition::Not(body) => matches!(
                body.as_ref(),
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(left, right),
                    true,
                ) if left == goal_left && right == goal_right
            ),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(left, right),
                false,
            ) => left == goal_left && right == goal_right,
            _ => false,
        };
        if !matches {
            continue;
        }
        let ClickProposition::Not(inner) = surface else {
            continue;
        };
        let (surface_left, surface_right) = surface_strict_parts(inner)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_not_lt_implies_ge".to_string(),
                    arguments: vec![surface_left, surface_right],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_greater_equal_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(goal_last, goal_first),
        true,
    ) = goal
    else {
        return None;
    };
    for (first_kernel, first_surface) in premise_pairs {
        let Some((first, middle)) = signed_nonstrict_parts(first_kernel) else {
            continue;
        };
        if first != goal_first.as_ref() {
            continue;
        }
        for (second_kernel, second_surface) in premise_pairs {
            let Some((second_middle, last)) = signed_nonstrict_parts(second_kernel) else {
                continue;
            };
            if second_middle != middle || last != goal_last.as_ref() {
                continue;
            }
            let (surface_first, surface_middle) = surface_nonstrict_parts(first_surface)?;
            let (_, surface_last) = surface_nonstrict_parts(second_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_ge_transitive".to_string(),
                        arguments: vec![surface_last, surface_middle, surface_first],
                    },
                    premises: vec![second_surface.clone(), first_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_negated_strict_successor_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(goal_value, goal_lower),
        true,
    ) = goal
    else {
        return None;
    };
    let Bitvector32Term::Constant(lower) = goal_lower.as_ref() else {
        return None;
    };
    let upper = (*lower as i32).checked_add(1)? as u32;
    for (kernel, surface) in premise_pairs {
        let (premise_value, premise_upper) = match kernel {
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(value, upper),
                    true,
                ) => (value.as_ref(), upper.as_ref()),
                _ => continue,
            },
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(value, upper),
                false,
            ) => (value.as_ref(), upper.as_ref()),
            _ => continue,
        };
        if premise_value != goal_value.as_ref()
            || premise_upper != &Bitvector32Term::Constant(upper)
        {
            continue;
        }
        let ClickProposition::Not(inner) = surface else {
            continue;
        };
        let (surface_value, surface_upper) = surface_strict_parts(inner)?;
        let surface_lower = ContractExpression::CFragment(CExpression::Value(int32(*lower)));
        let value_ge_upper = ClickProposition::Comparison {
            left: surface_value.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: surface_upper.clone(),
        };
        let upper_ge_lower = ClickProposition::Comparison {
            left: surface_upper.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: surface_lower.clone(),
        };
        return Some(vec![
            ProofTactic::Have(ProofHave {
                proposition: value_ge_upper.clone(),
                proof: SourceProof::Script(vec![
                    ProofTactic::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_not_lt_implies_ge".to_string(),
                            arguments: vec![surface_value.clone(), surface_upper.clone()],
                        },
                        premises: vec![surface.clone()],
                    },
                    ProofTactic::Assumption,
                ]),
            }),
            ProofTactic::Have(ProofHave {
                proposition: upper_ge_lower.clone(),
                proof: SourceProof::Script(vec![ProofTactic::Normalize]),
            }),
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_ge_transitive".to_string(),
                    arguments: vec![surface_value, surface_upper, surface_lower],
                },
                premises: vec![value_ge_upper, upper_ge_lower],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_increment_greater_equal_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(incremented, goal_lower),
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower.as_ref() || lower_base != base {
            continue;
        }
        let (surface_lower, surface_value) = surface_nonstrict_parts(lower_surface)?;
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let (_, surface_upper) = surface_strict_parts(upper_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_greater_equal_lower_bound".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![lower_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_increment_strict_greater_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterThan(incremented, goal_lower),
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower.as_ref() || lower_base != base {
            continue;
        }
        let (surface_lower, surface_value) = surface_nonstrict_parts(lower_surface)?;
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let (_, surface_upper) = surface_strict_parts(upper_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_strict_greater_lower_bound".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![lower_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_increment_strict_greater_from_strict_lower(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterThan(incremented, goal_lower),
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    let [(lower_kernel, lower_surface), (upper_kernel, upper_surface)] = premise_pairs else {
        return None;
    };
    let Some((premise_lower, lower_base)) = signed_strict_parts(lower_kernel) else {
        return None;
    };
    let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
        return None;
    };
    if premise_lower != goal_lower.as_ref() || lower_base != base || upper_base != base {
        return None;
    }
    let (surface_lower, surface_value) = surface_strict_parts(lower_surface)?;
    let (surface_upper_base, surface_upper) = surface_strict_parts(upper_surface)?;
    if surface_upper_base != surface_value {
        return None;
    }
    let weakened_lower = ClickProposition::Comparison {
        left: surface_lower.clone(),
        operator: ComparisonOperator::LessEqual,
        right: surface_value.clone(),
    };
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_lt_implies_le".to_string(),
                arguments: vec![surface_lower.clone(), surface_value.clone()],
            },
            premises: vec![lower_surface.clone()],
        },
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_increment_strict_greater_lower_bound".to_string(),
                arguments: vec![surface_value, surface_lower, surface_upper],
            },
            premises: vec![weakened_lower, upper_surface.clone()],
        },
        ProofTactic::Assumption,
    ])
}

fn plan_explicit_strict_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(goal_first, goal_last),
        true,
    ) = goal
    else {
        return None;
    };
    for (first_kernel, first_surface) in premise_pairs {
        let Some((first, middle)) = signed_strict_parts(first_kernel) else {
            continue;
        };
        if first != goal_first.as_ref() {
            continue;
        }
        for (second_kernel, second_surface) in premise_pairs {
            let Some((second_middle, last)) = signed_strict_parts(second_kernel) else {
                continue;
            };
            if second_middle != middle || last != goal_last.as_ref() {
                continue;
            }
            let (surface_first, surface_middle) = surface_strict_parts(first_surface)?;
            let (_, surface_last) = surface_strict_parts(second_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_lt_transitive".to_string(),
                        arguments: vec![surface_first, surface_middle, surface_last],
                    },
                    premises: vec![first_surface.clone(), second_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

/// A non-strict leg followed by a strict leg is strict end to end:
/// `first < last` follows from listed `first <= middle` and `middle < last`
/// through `int32_le_lt_transitive`, mirroring the strict-then-nonstrict
/// planner below.
fn plan_explicit_nonstrict_then_strict_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(goal_first, goal_last),
        true,
    ) = goal
    else {
        return None;
    };
    for (first_kernel, first_surface) in premise_pairs {
        let Some((first, middle)) = signed_nonstrict_parts(first_kernel) else {
            continue;
        };
        if first != goal_first.as_ref() {
            continue;
        }
        for (second_kernel, second_surface) in premise_pairs {
            let Some((second_middle, last)) = signed_strict_parts(second_kernel) else {
                continue;
            };
            if second_middle != middle || last != goal_last.as_ref() {
                continue;
            }
            let (surface_first, surface_middle) = surface_nonstrict_parts(first_surface)?;
            let (_, surface_last) = surface_strict_parts(second_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_le_lt_transitive".to_string(),
                        arguments: vec![surface_first, surface_middle, surface_last],
                    },
                    premises: vec![first_surface.clone(), second_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_strict_then_nonstrict_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(goal_first, goal_last),
        true,
    ) = goal
    else {
        return None;
    };
    for (first_kernel, first_surface) in premise_pairs {
        let Some((first, middle)) = signed_strict_parts(first_kernel) else {
            continue;
        };
        if first != goal_first.as_ref() {
            continue;
        }
        for (second_kernel, second_surface) in premise_pairs {
            let Some((second_middle, last)) = signed_nonstrict_parts(second_kernel) else {
                continue;
            };
            if second_middle != middle || last != goal_last.as_ref() {
                continue;
            }
            let (surface_first, surface_middle) = surface_strict_parts(first_surface)?;
            let (_, surface_last) = surface_nonstrict_parts(second_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_lt_le_transitive".to_string(),
                        arguments: vec![surface_first, surface_middle, surface_last],
                    },
                    premises: vec![first_surface.clone(), second_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

/// A constant non-strict upper bound sharpens below any larger constant:
/// `x < c1` follows from a listed `x <= c2` when `c2 < c1`, through
/// `int32_le_lt_transitive` over the context-free constant order.
fn plan_explicit_constant_strict_upper_bound_weakening(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(goal_value, goal_upper),
        true,
    ) = goal
    else {
        return None;
    };
    let Bitvector32Term::Constant(goal_constant) = goal_upper.as_ref() else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let Some((premise_value, premise_upper)) = signed_nonstrict_parts(premise_kernel) else {
            continue;
        };
        if premise_value != goal_value.as_ref() {
            continue;
        }
        let Bitvector32Term::Constant(premise_constant) = premise_upper else {
            continue;
        };
        if (*premise_constant as i32) >= (*goal_constant as i32) {
            continue;
        }
        let (surface_value, surface_premise_upper) = surface_nonstrict_parts(premise_surface)?;
        let goal_upper_surface = ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(*goal_constant),
        )));
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_le_lt_transitive".to_string(),
                    arguments: vec![surface_value, surface_premise_upper, goal_upper_surface],
                },
                premises: vec![premise_surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

/// An increment stays under a constant bound that clears its base's constant
/// bound: `x + 1 <= c1` follows from a listed `x <= c2` when `c2 < c1`,
/// through the strict weakening and `int32_increment_upper_bound`.
fn plan_explicit_increment_constant_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(incremented, goal_upper),
        true,
    ) = goal
    else {
        return None;
    };
    let base = increment_base(incremented)?;
    let Bitvector32Term::Constant(goal_constant) = goal_upper.as_ref() else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let Some((premise_value, premise_upper)) = signed_nonstrict_parts(premise_kernel) else {
            continue;
        };
        if premise_value != base {
            continue;
        }
        let Bitvector32Term::Constant(premise_constant) = premise_upper else {
            continue;
        };
        if (*premise_constant as i32) >= (*goal_constant as i32) {
            continue;
        }
        let (surface_value, surface_premise_upper) = surface_nonstrict_parts(premise_surface)?;
        let goal_upper_surface = ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(*goal_constant),
        )));
        let strict_surface = ClickProposition::Comparison {
            left: surface_value.clone(),
            operator: ComparisonOperator::LessThan,
            right: goal_upper_surface.clone(),
        };
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_le_lt_transitive".to_string(),
                    arguments: vec![
                        surface_value.clone(),
                        surface_premise_upper,
                        goal_upper_surface.clone(),
                    ],
                },
                premises: vec![premise_surface.clone()],
            },
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_upper_bound".to_string(),
                    arguments: vec![surface_value, goal_upper_surface],
                },
                premises: vec![strict_surface],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

/// A constant lower bound relaxes to any smaller constant: `c1 <= x` follows
/// from a listed `x >= c2` (in either spelling) when `c1 <= c2`, through
/// `int32_ge_transitive` over the context-free constant order and the
/// reversed-spelling theorem.
fn plan_explicit_constant_lower_bound_weakening(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, goal_value) = signed_nonstrict_parts(goal)?;
    let Bitvector32Term::Constant(goal_constant) = goal_lower else {
        return None;
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessEqual(_, _), true) = goal
    else {
        return None;
    };
    for (premise_kernel, premise_surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(premise_kernel) else {
            continue;
        };
        if premise_value != goal_value {
            continue;
        }
        let Bitvector32Term::Constant(premise_constant) = premise_lower else {
            continue;
        };
        if (*goal_constant as i32) > (*premise_constant as i32) || premise_constant == goal_constant
        {
            continue;
        }
        let (surface_premise_lower, surface_value) = surface_nonstrict_parts(premise_surface)?;
        let goal_lower_surface = ContractExpression::CFragment(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(*goal_constant),
        )));
        let weakened_surface = ClickProposition::Comparison {
            left: surface_value.clone(),
            operator: ComparisonOperator::GreaterEqual,
            right: goal_lower_surface.clone(),
        };
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_ge_transitive".to_string(),
                    arguments: vec![
                        surface_value.clone(),
                        surface_premise_lower,
                        goal_lower_surface.clone(),
                    ],
                },
                premises: vec![premise_surface.clone()],
            },
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_ge_implies_reversed_le".to_string(),
                    arguments: vec![surface_value, goal_lower_surface],
                },
                premises: vec![weakened_surface],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_strictly_positive_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, goal_value) = goal_exact_greater_equal_parts(goal)?;
    if goal_lower != &Bitvector32Term::Constant(0) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(0) || premise_value != goal_value {
            continue;
        }
        let (_, surface_value) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_strictly_positive_is_nonnegative".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_increment_below_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(value, amount),
        false,
    ) = goal
    else {
        return None;
    };
    if amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &Bitvector32Term::Constant(i32::MAX as u32) {
            continue;
        }
        let (surface_value, _) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_below_max_is_defined".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_one_plus_below_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedAddOverflows(one, value), false) =
        goal
    else {
        return None;
    };
    if one.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &Bitvector32Term::Constant(i32::MAX as u32) {
            continue;
        }
        let (surface_value, _) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_one_plus_below_max_is_defined".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_one_plus_strictly_increases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(value, sum), true) = goal
    else {
        return None;
    };
    let Bitvector32Term::Add(one, added_value) = sum.as_ref() else {
        return None;
    };
    if one.as_ref() != &Bitvector32Term::Constant(1) || added_value.as_ref() != value.as_ref() {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_value, upper)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || upper != &Bitvector32Term::Constant(i32::MAX as u32) {
            continue;
        }
        let (surface_value, _) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_one_plus_strictly_increases".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_nonnegative_add_within_max_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedAddOverflows(value, amount),
        false,
    ) = goal
    else {
        return None;
    };
    let zero = Bitvector32Term::Constant(0);
    let headroom = Bitvector32Term::Subtract(
        Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
        Box::new(amount.as_ref().clone()),
    );
    let (nonnegative_kernel, nonnegative_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| signed_nonstrict_parts(kernel) == Some((&zero, amount.as_ref())))?;
    let (headroom_kernel, headroom_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| signed_nonstrict_parts(kernel) == Some((value.as_ref(), &headroom)))?;
    let (_, surface_amount) = surface_nonstrict_parts(nonnegative_surface)?;
    let (surface_value, _) = surface_nonstrict_parts(headroom_surface)?;
    debug_assert_eq!(
        signed_nonstrict_parts(nonnegative_kernel),
        Some((&zero, amount.as_ref()))
    );
    debug_assert_eq!(
        signed_nonstrict_parts(headroom_kernel),
        Some((value.as_ref(), &headroom))
    );
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_nonnegative_add_within_max_is_defined".to_string(),
                arguments: vec![surface_value, surface_amount],
            },
            premises: vec![nonnegative_surface.clone(), headroom_surface.clone()],
        },
        ProofTactic::Assumption,
    ])
}

fn plan_explicit_nonnegative_subtract_within_value_is_defined(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedSubtractOverflows(value, amount),
        false,
    ) = goal
    else {
        return None;
    };
    let zero = Bitvector32Term::Constant(0);
    let (_, nonnegative_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| signed_nonstrict_parts(kernel) == Some((&zero, amount.as_ref())))?;
    let (_, within_value_surface) = premise_pairs.iter().find(|(kernel, _)| {
        signed_nonstrict_parts(kernel) == Some((amount.as_ref(), value.as_ref()))
    })?;
    let (_, surface_amount) = surface_nonstrict_parts(nonnegative_surface)?;
    let (_, surface_value) = surface_nonstrict_parts(within_value_surface)?;
    Some(vec![
        ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_nonnegative_subtract_within_value_is_defined".to_string(),
                arguments: vec![surface_value, surface_amount],
            },
            premises: vec![nonnegative_surface.clone(), within_value_surface.clone()],
        },
        ProofTactic::Assumption,
    ])
}

fn plan_explicit_positive_predecessor_is_nonnegative(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (goal_lower, predecessor) = goal_exact_less_equal_parts(goal)?;
    if goal_lower != &Bitvector32Term::Constant(0) {
        return None;
    }
    let Bitvector32Term::Subtract(value, amount) = predecessor else {
        return None;
    };
    if amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(0) || premise_value != value.as_ref() {
            continue;
        }
        let (_, surface_value) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_positive_predecessor_is_nonnegative".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

/// From `0 <= value` and `value <= bound`, the predecessor keeps the bound:
/// `value - 1 <= bound` through `int32_nonnegative_predecessor_upper_bound`.
/// When the nonnegativity leg is not itself a selected premise and
/// `spell_missing_leg` is set, a nested `have` derives it from the same
/// premises with the explicit equality-rewrite search (closing by a listed
/// premise or context-free normalization), so the emitted certificate still
/// names every dependency. Only outcome contexts pass `spell_missing_leg`:
/// a pure theorem proof has no `have`, so its planner must not emit one.
fn plan_explicit_predecessor_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    spell_missing_leg: bool,
) -> Option<Vec<ProofTactic>> {
    let (predecessor, goal_upper) = goal_exact_less_equal_parts(goal)?;
    let Bitvector32Term::Subtract(value, amount) = predecessor else {
        return None;
    };
    if amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (bound_kernel, bound_surface) in premise_pairs {
        let Some((premise_value, premise_bound)) = signed_nonstrict_parts(bound_kernel) else {
            continue;
        };
        if premise_value != value.as_ref() || premise_bound != goal_upper {
            continue;
        }
        let Some((surface_value, surface_bound)) = surface_nonstrict_parts(bound_surface) else {
            continue;
        };
        let nonnegative_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                value.clone(),
            ),
            true,
        );
        let mut tactics = Vec::new();
        let nonnegative_surface = if let Some((_, surface)) =
            premise_pairs.iter().find(|(kernel, _)| {
                signed_nonstrict_parts(kernel).is_some_and(|(lower, bounded)| {
                    lower == &Bitvector32Term::Constant(0) && bounded == value.as_ref()
                })
            }) {
            surface.clone()
        } else {
            if !spell_missing_leg {
                continue;
            }
            let kernel_premises = premise_pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            let Some(sub_tactics) = plan_explicit_equality_rewrites_from(
                &nonnegative_kernel,
                premise_pairs,
                &kernel_premises,
                &|current| {
                    kernel_premises
                        .iter()
                        .any(|fact| fact == current || condition_polarity_equivalent(fact, current))
                },
                &|_| None,
            ) else {
                continue;
            };
            let surface_zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
            let nonnegative = ClickProposition::Comparison {
                left: surface_zero,
                operator: ComparisonOperator::LessEqual,
                right: surface_value.clone(),
            };
            tactics.push(ProofTactic::Have(ProofHave {
                proposition: nonnegative.clone(),
                proof: SourceProof::Script(sub_tactics),
            }));
            nonnegative
        };
        tactics.push(ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: "int32_nonnegative_predecessor_upper_bound".to_string(),
                arguments: vec![surface_value, surface_bound],
            },
            premises: vec![nonnegative_surface, bound_surface.clone()],
        });
        tactics.push(ProofTactic::Assumption);
        return Some(tactics);
    }
    None
}

fn plan_explicit_one_le_predecessor(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (value, final_theorem) = if let Some((goal_lower, predecessor)) =
        goal_exact_less_equal_parts(goal)
    {
        if goal_lower != &Bitvector32Term::Constant(0) {
            return None;
        }
        let Bitvector32Term::Subtract(value, amount) = predecessor else {
            return None;
        };
        if amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        (value.as_ref(), "int32_positive_predecessor_is_nonnegative")
    } else {
        let (predecessor, value) = goal_exact_less_than_parts(goal)?;
        let Bitvector32Term::Subtract(predecessor_value, amount) = predecessor else {
            return None;
        };
        if predecessor_value.as_ref() != value || amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        (value, "int32_positive_predecessor_strictly_decreases")
    };
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_nonstrict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(1) || premise_value != value {
            continue;
        }
        let (_, surface_value) = surface_nonstrict_parts(surface)?;
        let surface_zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
        let positive = ClickProposition::Comparison {
            left: surface_zero.clone(),
            operator: ComparisonOperator::LessThan,
            right: surface_value.clone(),
        };
        return Some(vec![
            ProofTactic::Have(ProofHave {
                proposition: positive.clone(),
                proof: SourceProof::Script(vec![
                    ProofTactic::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_successor_le_implies_lt".to_string(),
                            arguments: vec![surface_zero, surface_value.clone()],
                        },
                        premises: vec![surface.clone()],
                    },
                    ProofTactic::Assumption,
                ]),
            }),
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: final_theorem.to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![positive],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_positive_predecessor_strictly_decreases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (predecessor, value) = goal_exact_less_than_parts(goal)?;
    let Bitvector32Term::Subtract(predecessor_value, amount) = predecessor else {
        return None;
    };
    if predecessor_value.as_ref() != value || amount.as_ref() != &Bitvector32Term::Constant(1) {
        return None;
    }
    for (kernel, surface) in premise_pairs {
        let Some((premise_lower, premise_value)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_lower != &Bitvector32Term::Constant(0) || premise_value != value {
            continue;
        }
        let (_, surface_value) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_positive_predecessor_strictly_decreases".to_string(),
                    arguments: vec![surface_value],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_le_and_not_lt_implies_eq(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
        return None;
    };
    for (le_kernel, le_surface) in premise_pairs {
        let Some((le_left, le_right)) = signed_nonstrict_parts(le_kernel) else {
            continue;
        };
        if le_left != left.as_ref() || le_right != right.as_ref() {
            continue;
        }
        for (not_lt_kernel, not_lt_surface) in premise_pairs {
            let matches_not_lt = match not_lt_kernel {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(not_left, not_right),
                    false,
                ) => not_left.as_ref() == left.as_ref() && not_right.as_ref() == right.as_ref(),
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedLessThan(not_left, not_right),
                        true,
                    ) if not_left.as_ref() == left.as_ref()
                        && not_right.as_ref() == right.as_ref()
                ),
                _ => false,
            };
            if !matches_not_lt {
                continue;
            }
            let (surface_left, surface_right) = surface_nonstrict_parts(le_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_le_and_not_lt_implies_eq".to_string(),
                        arguments: vec![surface_left, surface_right],
                    },
                    premises: vec![le_surface.clone(), not_lt_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_ge_and_not_gt_implies_eq(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = goal else {
        return None;
    };
    for (ge_kernel, ge_surface) in premise_pairs {
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(ge_left, ge_right),
            true,
        ) = ge_kernel
        else {
            continue;
        };
        if ge_left != left || ge_right != right {
            continue;
        }
        for (not_gt_kernel, not_gt_surface) in premise_pairs {
            let matches_not_gt = match not_gt_kernel {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterThan(not_left, not_right),
                    false,
                ) => not_left == left && not_right == right,
                Proposition::Not(body) => matches!(
                    body.as_ref(),
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedGreaterThan(not_left, not_right),
                        true,
                    ) if not_left == left && not_right == right
                ),
                _ => false,
            };
            if !matches_not_gt {
                continue;
            }
            let (surface_right, surface_left) = surface_nonstrict_parts(ge_surface)?;
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_ge_and_not_gt_implies_eq".to_string(),
                        arguments: vec![surface_left, surface_right],
                    },
                    premises: vec![ge_surface.clone(), not_gt_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_increment_strictly_increases(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (base, incremented) = goal_exact_less_than_parts(goal)?;
    if increment_base(incremented)? != base {
        return None;
    }

    for (kernel, surface) in premise_pairs {
        let Some((premise_base, _)) = signed_strict_parts(kernel) else {
            continue;
        };
        if premise_base != base {
            continue;
        }
        let (value, upper) = surface_strict_parts(surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_increment_strictly_increases".to_string(),
                    arguments: vec![value, upper],
                },
                premises: vec![surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_successor_le_implies_lt(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let (lower, value) = goal_exact_less_than_parts(goal)?;
    for (bound_kernel, bound_surface) in premise_pairs {
        let Some((successor, bound_value)) = signed_nonstrict_parts(bound_kernel) else {
            continue;
        };
        if bound_value != value
            || successor != &Bitvector32Term::add(lower.clone(), Bitvector32Term::Constant(1))
        {
            continue;
        }
        let no_overflow = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(lower.clone()),
                Box::new(successor.clone()),
            ),
            true,
        );
        if !normalizes_context_free(&no_overflow) {
            continue;
        }
        let Bitvector32Term::Constant(lower) = lower else {
            continue;
        };
        let surface_lower = ContractExpression::CFragment(CExpression::Value(int32(*lower)));
        let (_, surface_value) = surface_nonstrict_parts(bound_surface)?;
        return Some(vec![
            ProofTactic::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "int32_successor_le_implies_lt".to_string(),
                    arguments: vec![surface_lower, surface_value],
                },
                premises: vec![bound_surface.clone()],
            },
            ProofTactic::Assumption,
        ]);
    }
    None
}

fn plan_explicit_increment_preserves_order(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    for (order_kernel, order_surface) in premise_pairs {
        let Some((lower, value)) = signed_nonstrict_parts(order_kernel) else {
            continue;
        };
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_value, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_value != value {
                continue;
            }
            let expected = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::add(
                        lower.clone(),
                        Bitvector32Term::Constant(1),
                    )),
                    Box::new(Bitvector32Term::add(
                        value.clone(),
                        Bitvector32Term::Constant(1),
                    )),
                ),
                true,
            );
            if &expected != goal {
                continue;
            }
            let Some((surface_lower, _)) = surface_nonstrict_parts(order_surface) else {
                continue;
            };
            let Some((surface_value, surface_upper)) = surface_strict_parts(upper_surface) else {
                continue;
            };
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_preserves_order".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![order_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

fn plan_explicit_increment_lower_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // The theorem concludes in less-equal orientation; a greater-equal goal
    // spelling belongs to `int32_increment_greater_equal_lower_bound`, whose
    // conclusion the closing `assumption` can match exactly.
    let (goal_lower, incremented) = goal_exact_less_equal_parts(goal)?;
    let base = increment_base(incremented)?;

    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((premise_lower, lower_base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if premise_lower != goal_lower || lower_base != base {
            continue;
        }
        let Some((surface_lower, _)) = surface_nonstrict_parts(lower_surface) else {
            continue;
        };
        for (upper_kernel, upper_surface) in premise_pairs {
            let Some((upper_base, _)) = signed_strict_parts(upper_kernel) else {
                continue;
            };
            if upper_base != base {
                continue;
            }
            let Some((surface_value, surface_upper)) = surface_strict_parts(upper_surface) else {
                continue;
            };
            return Some(vec![
                ProofTactic::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_increment_lower_bound".to_string(),
                        arguments: vec![surface_value, surface_lower, surface_upper],
                    },
                    premises: vec![lower_surface.clone(), upper_surface.clone()],
                },
                ProofTactic::Assumption,
            ]);
        }
    }
    None
}

pub(super) fn plan_restricted_simp_expansion(
    goal: &Proposition,
    surface_goal: Option<&ClickProposition>,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Result<Vec<ProofTactic>, ClickError> {
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let derivation = plan_restricted_simp_goal(goal, available.clone(), goal, &available)
        .map_err(ClickError::new)?;
    lower_restricted_simp_plan(
        goal,
        surface_goal,
        &SimpEvidence::Derivation(derivation),
        premise_pairs,
    )
}

fn collect_definable_predicate_names(
    proposition: &Proposition,
    predicate_environment: &PredicateEnvironment,
    names: &mut Vec<String>,
) {
    match proposition {
        Proposition::Predicate { name, .. } => {
            if predicate_environment.get(name).is_some() && !names.contains(name) {
                names.push(name.clone());
            }
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_definable_predicate_names(left, predicate_environment, names);
            collect_definable_predicate_names(right, predicate_environment, names);
        }
        Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
            collect_definable_predicate_names(body, predicate_environment, names);
        }
        _ => {}
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_outcome_simp_proof(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<SourceProof, ClickError> {
    // An opaque predicate in the goal is unfolded by the certificate: the
    // replay-side derivation judgment has no predicate rules, so the
    // emitted proof must carry `unfold(...)` and prove the body. The goal
    // comparison in the caller keeps working because it accepts the goal
    // in either spelling.
    // The emitted have script must carry its own unfolds: replay lowers the
    // surface proposition under exactly the unfolds written in the script,
    // while the kernel goal here was lowered with the drain's unfold set
    // active. Two cases produce a spelling gap. (a) The kernel goal still
    // holds an opaque predicate: unfold it and prove the body — the
    // replay-side derivation judgment has no predicate rules. (b) The
    // kernel goal is already the unfolded body while the surface goal is a
    // predicate call: without the prefix, replay would lower the surface
    // goal opaquely and prove a different proposition than the tactics
    // certify.
    let mut opaque_names = Vec::new();
    collect_definable_predicate_names(goal, predicate_environment, &mut opaque_names);
    if !opaque_names.is_empty() {
        // Best effort: a deliberately opaque predicate (whose body's loads
        // the contract does not establish) fails to unfold here; such goals
        // must close without unfolding, so fall through to the direct path.
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &opaque_names,
            goal,
            &assumptions_from_propositions(available),
        );
        if let Ok(unfolded_goal) = unfolded {
            let mut unfolding_replay = replay.clone();
            unfolding_replay
                .unfolded_predicates
                .extend(opaque_names.iter().cloned());
            // Unfold the surface goal in step with the kernel goal: the
            // structural certificate constructor matches surface and kernel
            // shapes together, so a predicate body that unfolds to a
            // conjunction only splits when the surface spelling is the body
            // conjunction too. The emitted `unfold(...)` prefix makes replay
            // lower the inner spellings under the same unfolds. Non-And
            // bodies keep the predicate-call spelling: the universal-goal
            // machinery matches the call form and unfolds on its own terms.
            let unfolded_surface = unfold_structural_invariant_proposition(
                predicate_environment,
                surface_goal,
                &opaque_names,
            )
            .ok()
            .filter(|unfolded_surface| {
                matches!(unfolded_surface, ClickProposition::And(_, _))
                    && matches!(unfolded_goal, Proposition::And(_, _))
            })
            .unwrap_or_else(|| surface_goal.clone());
            if let Ok(SourceProof::Script(inner_tactics)) = lower_outcome_simp_proof_direct(
                &unfolding_replay,
                &unfolded_surface,
                &unfolded_goal,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            ) {
                let mut tactics = opaque_names
                    .into_iter()
                    .map(ProofTactic::UnfoldPredicate)
                    .collect::<Vec<_>>();
                tactics.extend(inner_tactics);
                return Ok(SourceProof::Script(tactics));
            }
        }
    } else {
        // Carry the drain's whole unfold set: replay lowers the goal AND
        // every listed premise under the script's unfolds, and a premise
        // can be an unfold-active predicate call even when the goal is not.
        let mut surface_names = replay.unfolded_predicates.clone();
        surface_names.retain(|name| predicate_environment.get(name).is_some());
        if !surface_names.is_empty() {
            // The kernel goal was lowered with these unfolds active, so a
            // predicate-call surface spelling here already stands for its
            // body. Unfold the surface goal to the matching body spelling so
            // the structural constructor can split a body conjunction; the
            // emitted `unfold(...)` prefix reproduces the same spelling
            // during replay. Non-And bodies keep the predicate-call
            // spelling for the universal-goal machinery.
            let unfolded_surface = unfold_structural_invariant_proposition(
                predicate_environment,
                surface_goal,
                &surface_names,
            )
            .ok()
            .filter(|unfolded_surface| {
                matches!(unfolded_surface, ClickProposition::And(_, _))
                    && matches!(goal, Proposition::And(_, _))
            })
            .unwrap_or_else(|| surface_goal.clone());
            let inner = lower_outcome_simp_proof_direct(
                replay,
                &unfolded_surface,
                goal,
                available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            )?;
            let SourceProof::Script(inner_tactics) = inner else {
                return Err(ClickError::new(
                    "predicate-goal certificate lowering produced a non-script proof",
                ));
            };
            let mut tactics = surface_names
                .into_vec()
                .into_iter()
                .map(ProofTactic::UnfoldPredicate)
                .collect::<Vec<_>>();
            tactics.extend(inner_tactics);
            return Ok(SourceProof::Script(tactics));
        }
    }
    lower_outcome_simp_proof_direct(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_outcome_simp_proof_direct(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<SourceProof, ClickError> {
    if let (
        ClickProposition::Implies(_, surface_consequent),
        Proposition::Implies(antecedent, consequent),
    ) = (surface_goal, goal)
        && !available.contains(goal)
    {
        if let Ok(tactics) = lower_outcome_simp_tactics(
            replay,
            surface_goal,
            goal,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        ) {
            return Ok(SourceProof::Script(tactics));
        }
        let mut consequent_available = available.to_vec();
        if !consequent_available.contains(antecedent) {
            consequent_available.push(antecedent.as_ref().clone());
        }
        let proof = lower_outcome_simp_proof(
            replay,
            surface_consequent,
            consequent,
            &consequent_available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        )?;
        let SourceProof::Script(mut tactics) = proof else {
            return Err(ClickError::new(
                "implication certificate lowering produced a non-script proof",
            ));
        };
        tactics.insert(0, ProofTactic::Intro);
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "implication derivation produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok(SourceProof::Script(tactics));
    }
    if let (ClickProposition::Or(surface_left, surface_right), Proposition::Or(left, right)) =
        (surface_goal, goal)
        && !available.contains(goal)
    {
        // Prefer a whole-goal certificate (assumption, transport, or an
        // explicit `cases` split over a disjunctive premise). Only when that
        // fails, introduce one spelled disjunct with `left()`/`right()`.
        let direct = lower_outcome_simp_tactics(
            replay,
            surface_goal,
            goal,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        );
        let direct_error = match direct {
            Ok(tactics) => return Ok(SourceProof::Script(tactics)),
            Err(error) => error,
        };
        for (side_surface, side_kernel, choose) in [
            (surface_left, left, ProofTactic::Left),
            (surface_right, right, ProofTactic::Right),
        ] {
            if pure_fact_is_replay_available(side_kernel, available) {
                return Ok(SourceProof::Script(vec![choose]));
            }
            let Ok(proof) = lower_outcome_simp_proof(
                replay,
                side_surface,
                side_kernel,
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
            let tactics = vec![
                ProofTactic::Have(ProofHave {
                    proposition: side_surface.as_ref().clone(),
                    proof,
                }),
                choose,
            ];
            ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "disjunct introduction produced a non-simple expansion: {error:?}"
                ))
            })?;
            return Ok(SourceProof::Script(tactics));
        }
        return Err(direct_error);
    }
    if let (ClickProposition::And(surface_left, surface_right), Proposition::And(left, right)) =
        (surface_goal, goal)
        && !available.contains(goal)
    {
        let left_proof = lower_outcome_simp_proof(
            replay,
            surface_left,
            left,
            available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        )?;
        let mut right_available = available.to_vec();
        if !right_available.contains(left) {
            right_available.push(left.as_ref().clone());
        }
        let right_proof = lower_outcome_simp_proof(
            replay,
            surface_right,
            right,
            &right_available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        )?;
        return Ok(SourceProof::Script(vec![
            ProofTactic::Have(ProofHave {
                proposition: surface_left.as_ref().clone(),
                proof: left_proof,
            }),
            ProofTactic::Have(ProofHave {
                proposition: surface_right.as_ref().clone(),
                proof: right_proof,
            }),
            ProofTactic::Split,
        ]));
    }
    Ok(SourceProof::Script(lower_outcome_simp_tactics(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?))
}

#[allow(clippy::too_many_arguments)]
fn certify_outcome_simp_have(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    claim_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<Vec<ProofTactic>, ClickError> {
    // First require an explicit proof plan for the claim itself. The final
    // proof is rebuilt below after its separately certified loadability
    // obligations have been added to the replay context.
    lower_outcome_simp_proof(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?;
    let mut goal_lowering_facts = available.to_vec();
    let lowered = lower_outcome_proposition_with_obligations(
        parameters,
        arguments,
        pre_state,
        post_state,
        Some(result),
        &goal_lowering_facts,
        surface_goal,
        predicate_environment,
        click_function_environment,
        &replay.program_point_states,
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` could not structurally lower its surface goal: {error}"
        ))
    })?;
    // The claim goal may have been lowered while `unfold(...)` was active,
    // so compare against the re-lowered goal in the same unfolded spelling.
    let lowered_proposition = if replay.unfolded_predicates.is_empty() {
        lowered.proposition.clone()
    } else {
        unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            &lowered.proposition,
            &assumptions_from_propositions(available),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` could not unfold its re-lowered goal: {message}"
            ))
        })?
    };
    if normalize_direct_atomic_memory_loads(&lowered.proposition)
        != normalize_direct_atomic_memory_loads(goal)
        && normalize_direct_atomic_memory_loads(&lowered_proposition)
            != normalize_direct_atomic_memory_loads(goal)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` surface goal lowered to a different kernel proposition\n  planned: {}\n  lowered: {}\n  unfolded lowering: {}",
            describe_pure_fact(goal, parameters, arguments),
            describe_pure_fact(&lowered.proposition, parameters, arguments),
            describe_pure_fact(&lowered_proposition, parameters, arguments),
        )));
    }

    // A claim lowered under an active top-level predicate unfold may need its
    // certificate to state the body explicitly. Choose that spelling only
    // when lowering it in this same context reproduces the exact kernel goal;
    // predicates whose surface lowering carries distinct binding information
    // retain their original spelling.
    let certificate_surface_goal = match surface_goal {
        ClickProposition::PredicateCall { name, .. }
            if replay
                .unfolded_predicates
                .iter()
                .any(|unfolded| unfolded == name) =>
        {
            let unfolded_surface = unfold_structural_invariant_proposition(
                predicate_environment,
                surface_goal,
                &replay.unfolded_predicates,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` could not express its unfolded certificate goal: {message}"
                ))
            })?;
            let unfolded_lowering = lower_outcome_proposition_with_obligations(
                parameters,
                arguments,
                pre_state,
                post_state,
                Some(result),
                &goal_lowering_facts,
                &unfolded_surface,
                predicate_environment,
                click_function_environment,
                &replay.program_point_states,
            );
            if unfolded_lowering.is_ok_and(|lowered| {
                normalize_direct_atomic_memory_loads(&lowered.proposition)
                    == normalize_direct_atomic_memory_loads(goal)
            }) {
                unfolded_surface
            } else {
                surface_goal.clone()
            }
        }
        _ => surface_goal.clone(),
    };

    let mut certified_available = available.to_vec();
    for fact in crate::kernel::certified_store_loadability_facts(&replay.effect_facts) {
        if !certified_available.contains(&fact) {
            certified_available.push(fact);
        }
    }
    let mut surface_tactics = Vec::new();
    let mut quantified_memory_premises: Vec<(ClickProposition, Proposition)> = Vec::new();
    'obligations: for obligation in lowered.loadability_obligations {
        let SurfaceLoadabilityObligation {
            proposition: obligation,
            segment,
        } = obligation;
        if exact_fact_is_available(&obligation, &certified_available) {
            continue;
        }
        let mut coverage_context = certified_available.clone();
        for fact in &replay.effect_facts {
            if !coverage_context.contains(fact.proposition()) {
                coverage_context.push(fact.proposition().clone());
            }
        }
        if crate::kernel::loadable_covered_by_fact(
            &assumptions_from_propositions(&coverage_context),
            &obligation,
        ) {
            certified_available.push(obligation);
            continue;
        }
        for source in crate::kernel::certified_store_loadability_facts(&replay.effect_facts) {
            let transition_facts = fact_transport_transition_facts(&replay.effect_facts, &source);
            let transport_assumptions = transition_facts
                .iter()
                .fold(
                    assumptions_from_propositions(&coverage_context),
                    |assumptions, fact| assumptions.assume_proposition(fact.proposition().clone()),
                )
                .assume_proposition(source.clone());
            if certified_fact_transport_reaches(
                &source,
                &obligation,
                post_state.memory(),
                &transport_assumptions,
            ) {
                certified_available.push(obligation);
                continue 'obligations;
            }
        }
        let recorded_segment = segment.clone();
        let check_surface = |surface: &ClickProposition| {
            lower_outcome_proposition_with_program_points(
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                &certified_available,
                surface,
                predicate_environment,
                click_function_environment,
                &replay.program_point_states,
            )
            .is_ok_and(|lowered| lowered == obligation)
        };
        let mut surface_obligation = segment.map(|segment| ClickProposition::Loadable { segment });
        if surface_obligation
            .as_ref()
            .is_some_and(|surface| !check_surface(surface))
            && let Some(ClickProposition::Loadable { segment }) = &surface_obligation
        {
            let mut old_segment = segment.clone();
            old_segment.state = ContractSegmentState::Old;
            let old = ClickProposition::Loadable {
                segment: old_segment,
            };
            surface_obligation = check_surface(&old).then_some(old);
        }
        let surface_obligation = match surface_obligation.filter(|surface| check_surface(surface)) {
            Some(surface) => surface,
            None => match checked_surface_fact_at_outcome(
                replay,
                &obligation,
                SurfaceFactMatch::CanonicalExact,
                &certified_available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
            ) {
                Ok(surface) => surface,
                Err(error) => {
                    // A loadability obligation inside a quantified body can
                    // mention the binder and therefore has no standalone
                    // Surface Click spelling. It is safe to leave implicit
                    // only when ordinary (non-deferred) lowering of the whole
                    // goal proves it from the explicit generated premises.
                    if quantified_memory_premises.is_empty()
                        && matches!(
                            goal,
                            Proposition::ForAll { .. } | Proposition::Exists { .. }
                        )
                    {
                        let mut atomic_available = Vec::new();
                        for fact in available {
                            atomic_conjuncts(fact, &mut atomic_available);
                        }
                        for fact in atomic_available {
                            let needed_for_lowering =
                                matches!(fact, Proposition::CMemoryLoadable { .. })
                                    || matches!(fact, Proposition::ConditionIs(_, _))
                                        && c_condition_fact_has_memory(fact);
                            if !needed_for_lowering {
                                continue;
                            }
                            if let Ok(surface) = checked_surface_fact_at_outcome(
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
                            ) && !quantified_memory_premises
                                .iter()
                                .any(|(recorded, _)| recorded == &surface)
                            {
                                quantified_memory_premises.push((surface, fact.clone()));
                            }
                        }
                    }
                    for (_, fact) in &quantified_memory_premises {
                        if !goal_lowering_facts.contains(fact) {
                            goal_lowering_facts.push(fact.clone());
                        }
                    }
                    let implicit_lowering = lower_outcome_proposition_with_program_points(
                        parameters,
                        arguments,
                        pre_state,
                        post_state,
                        result,
                        &goal_lowering_facts,
                        surface_goal,
                        predicate_environment,
                        click_function_environment,
                        &replay.program_point_states,
                    );
                    let implicit_in_goal = implicit_lowering.is_ok_and(|lowered_goal| {
                        normalize_direct_atomic_memory_loads(&lowered_goal)
                            == normalize_direct_atomic_memory_loads(goal)
                    });
                    if implicit_in_goal {
                        continue;
                    }
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` loadability obligation has no exact surface spelling: {}\n  recorded segment: {recorded_segment:?}\n  obligation: {obligation:?}",
                        error.message(),
                    )));
                }
            },
        };
        let obligation_memory = match &obligation {
            Proposition::CMemoryLoadable { memory, .. } => memory,
            _ => unreachable!("surface lowering obligations are loadability propositions"),
        };
        let has_current_loadability_context = certified_available.iter().any(|fact| {
            matches!(fact, Proposition::CMemoryLoadable { memory, .. }
                if memory.has_same_snapshot_markers(obligation_memory))
        });
        let direct = has_current_loadability_context
            .then(|| {
                lower_outcome_simp_proof(
                    replay,
                    &surface_obligation,
                    &obligation,
                    &certified_available,
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    result,
                    predicate_environment,
                    click_function_environment,
                )
            })
            .transpose()
            .and_then(|proof| {
                proof.ok_or_else(|| {
                    ClickError::new("loadability obligation requires memory transport")
                })
            })
            .and_then(|proof| {
                let surface_have = ProofHave {
                    proposition: surface_obligation.clone(),
                    proof,
                };
                let replayed = prove_have_at_point(
                    &surface_have,
                    theorem_environment,
                    claim_label,
                    tactic_index,
                    &certified_available,
                    &replay.effect_facts,
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    Some(result),
                    &replay.program_point_states,
                    Some(&replay.surface_propositions),
                    predicate_environment,
                    click_function_environment,
                    function_requires,
                    Some(path_index),
                )?;
                if replayed != obligation {
                    return Err(ClickError::new(
                        "loadability certificate replayed a different proposition",
                    ));
                }
                Ok(surface_have)
            });
        if let Ok(surface_have) = direct {
            certified_available.push(obligation);
            surface_tactics.push(ProofTactic::Have(surface_have));
            continue;
        }

        let Proposition::CMemoryLoadable { .. } = &obligation else {
            unreachable!("surface lowering obligations are loadability propositions")
        };
        let source_selectors = std::iter::once(VisitSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }))
        .chain(
            replay
                .program_point_states
                .keys()
                .rev()
                .cloned()
                .map(VisitSelector::ProgramPoint),
        );
        let source_candidates = source_selectors
            .filter_map(|selector| {
                let surface = ClickProposition::At {
                    selector,
                    proposition: Box::new(surface_obligation.clone()),
                };
                let source = lower_outcome_proposition_with_program_points(
                    parameters,
                    arguments,
                    pre_state,
                    post_state,
                    result,
                    &certified_available,
                    &surface,
                    predicate_environment,
                    click_function_environment,
                    &replay.program_point_states,
                )
                .ok()?;
                matches!(source, Proposition::CMemoryLoadable { .. }).then_some((source, surface))
            })
            .fold(Vec::new(), |mut candidates, candidate| {
                if !candidates.iter().any(|(source, _)| source == &candidate.0) {
                    candidates.push(candidate);
                }
                candidates
            });
        let source_candidate_count = source_candidates.len();
        let mut derivable_source_count = 0;
        let mut transportable_source_count = 0;
        let transported = source_candidates
            .into_iter()
            .find_map(|(source, surface_source)| {
                let Proposition::CMemoryLoadable {
                    memory: source_memory,
                    ..
                } = &source
                else {
                    unreachable!("loadability source candidates are loadability propositions")
                };
                let derivation = if exact_fact_is_available(&source, &certified_available) {
                    None
                } else {
                    let source_context = certified_available
                        .iter()
                        .filter(|fact| {
                            matches!(fact, Proposition::ConditionIs(_, _))
                                || matches!(fact, Proposition::CMemoryLoadable { memory, .. }
                                if memory.has_same_snapshot_markers(source_memory))
                        })
                        .cloned()
                        .collect::<Vec<_>>();
                    Some(
                        assumptions_from_propositions(&source_context)
                            .derive_atomic_proposition(&source)
                            .or_else(|| {
                                // The marker filter can starve the context;
                                // retry over everything available plus the
                                // path's effect facts, which connect the
                                // snapshots loadability transports across.
                                let mut context = certified_available.clone();
                                for fact in &replay.effect_facts {
                                    if !context.contains(fact.proposition()) {
                                        context.push(fact.proposition().clone());
                                    }
                                }
                                assumptions_from_propositions(&context)
                                    .derive_atomic_proposition(&source)
                            })?,
                    )
                };
                derivable_source_count += 1;
                let transition_facts =
                    fact_transport_transition_facts(&replay.effect_facts, &source);
                let transport_assumptions = transition_facts
                    .iter()
                    .fold(
                        assumptions_from_propositions(&certified_available),
                        |assumptions, fact| {
                            assumptions.assume_proposition(fact.proposition().clone())
                        },
                    )
                    .assume_proposition(source.clone());
                let reaches = certified_fact_transport_reaches(
                    &source,
                    &obligation,
                    post_state.memory(),
                    &transport_assumptions,
                );
                transportable_source_count += usize::from(reaches);
                reaches.then_some((source, surface_source, derivation, transition_facts))
            });
        let Some((source, surface_source, source_derivation, transition_facts)) = transported
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: loadability obligation has neither a direct proof nor a certified transport\n  surface obligation: {}\n  source candidates: {source_candidate_count}, derivable: {derivable_source_count}, transportable: {transportable_source_count}\n  obligation: {obligation:?}",
                describe_click_proposition(&surface_obligation),
            )));
        };
        if !exact_fact_is_available(&source, &certified_available) {
            let source_derivation = source_derivation.expect(
                "a non-exact loadability transport source must carry its checked derivation",
            );
            let (_, source_proof) = lower_surface_atomic_derivation(
                replay,
                &source_derivation,
                Some(&surface_source),
                None,
                &certified_available,
                parameters,
                arguments,
                post_state,
                predicate_environment,
                click_function_environment,
            )?;
            let source_have = ProofHave {
                proposition: surface_source.clone(),
                proof: source_proof,
            };
            let replayed = prove_have_at_point(
                &source_have,
                theorem_environment,
                claim_label,
                tactic_index,
                &certified_available,
                &replay.effect_facts,
                parameters,
                arguments,
                pre_state,
                post_state,
                Some(result),
                &replay.program_point_states,
                Some(&replay.surface_propositions),
                predicate_environment,
                click_function_environment,
                function_requires,
                Some(path_index),
            )?;
            if replayed != source {
                return Err(ClickError::new(
                    "loadability transport source replayed a different proposition",
                ));
            }
            certified_available.push(source.clone());
            surface_tactics.push(ProofTactic::Have(source_have));
        }
        let explicit_assumptions = assumptions_from_propositions(std::slice::from_ref(&source));
        let resource_facts = post_state
            .resources()
            .observable_facts_assuming_valid(&explicit_assumptions);
        let transport_assumptions = certified_available
            .iter()
            .filter(|fact| is_implicit_fact_transport_context(fact))
            .cloned()
            .chain(resource_facts)
            .fold(explicit_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        let transport_assumptions = transition_facts
            .iter()
            .fold(transport_assumptions, |assumptions, fact| {
                assumptions.assume_proposition(fact.proposition().clone())
            })
            .assume_proposition(source.clone());
        if !certified_fact_transport_reaches(
            &source,
            &obligation,
            post_state.memory(),
            &transport_assumptions,
        ) {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: explicit loadability source does not replay its certified transport"
            )));
        }
        surface_tactics.push(ProofTactic::TransportUsing {
            source: surface_source.clone(),
            target: surface_obligation,
            premises: vec![surface_source],
        });
        certified_available.push(obligation);
    }

    let proof = lower_outcome_simp_proof(
        replay,
        surface_goal,
        goal,
        &certified_available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
    )?;
    let surface_have = ProofHave {
        proposition: certificate_surface_goal,
        proof,
    };
    let surface_tactic = ProofTactic::Have(surface_have.clone());
    let certificate = ProofCertificate::from_proof_tactics(std::slice::from_ref(&surface_tactic))
        .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` produced an invalid certificate: {error:?}"
        ))
    })?;
    // Replay may frame loads across recorded effects; a fresh replay
    // recomputes the same effect facts from execution, so including them
    // keeps in-place and standalone replays aligned.
    let mut replay_available = certified_available.clone();
    for fact in &replay.effect_facts {
        if !replay_available.contains(fact.proposition()) {
            replay_available.push(fact.proposition().clone());
        }
    }
    for equation in crate::kernel::certified_store_equations(&replay.effect_facts) {
        if !replay_available.contains(&equation) {
            replay_available.push(equation);
        }
    }
    let replayed_goal = prove_have_at_point(
        &surface_have,
        theorem_environment,
        claim_label,
        tactic_index,
        &replay_available,
        &replay.effect_facts,
        parameters,
        arguments,
        pre_state,
        post_state,
        Some(result),
        &replay.program_point_states,
        Some(&replay.surface_propositions),
        predicate_environment,
        click_function_environment,
        function_requires,
        Some(path_index),
    )
    .map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` certificate failed replay:\n{}\n{}",
            format_proof_certificate(&certificate),
            error.message(),
        ))
    })?;
    if replayed_goal != *goal {
        // The claim goal may be spelled with `unfold(...)` active while the
        // replay produces the folded predicate; both name one proposition by
        // the predicate's definition.
        let replayed_unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &replay.unfolded_predicates,
            &replayed_goal,
            &assumptions_from_propositions(&replay_available),
        );
        if replay.unfolded_predicates.is_empty() || replayed_unfolded.as_ref() != Ok(goal) {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` certificate replayed a different goal"
            )));
        }
    }
    surface_tactics.push(surface_tactic);
    Ok(surface_tactics)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn certify_outcome_simp(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    claim_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<ProofCertificate, ClickError> {
    let mut surface_tactics = certify_outcome_simp_have(
        replay,
        surface_goal,
        goal,
        available,
        parameters,
        arguments,
        pre_state,
        post_state,
        result,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        function_requires,
        claim_label,
        tactic_index,
        path_index,
    )?;
    surface_tactics.push(ProofTactic::Assumption);
    let certificate = ProofCertificate::from_proof_tactics(&surface_tactics).map_err(|error| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}, tactic {tactic_index}: smart `simp` produced an invalid certificate: {error:?}"
        ))
    })?;
    Ok(certificate)
}

/// Lower an exit-claim `simp` that closed under pending `witness`/`choose`
/// tactics.
///
/// `witness` and `choose` are simple tactics, and a `have` proof admits
/// them (`prove_pure_proposition_case_at_point` runs both). So the closer
/// lowers to `have <claim goal> by { <existence tactics>, <simple closer> }`
/// followed by `assumption`: the have re-derives the existential inside its
/// own scope, and `assumption` discharges the claim from the fact the have
/// established. The have's proposition is the claim's own surface goal, so
/// no new surface spelling has to be synthesized for the instantiated body.
///
/// Every candidate is accepted only if `prove_have_at_point` — the replay
/// judgment itself — proves it and yields the claim's kernel goal, so this
/// emits exactly what replay accepts.
#[allow(clippy::too_many_arguments)]
pub(super) fn certify_outcome_existential_simp(
    replay: &TacticReplayState,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    available: &[Proposition],
    existence_tactics: &[ProofTactic],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    claim_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<ProofCertificate, ClickError> {
    // Replay may frame loads across recorded effects; a fresh replay
    // recomputes the same effect facts from execution, so including them
    // keeps in-place and standalone replays aligned.
    let mut replay_available = available.to_vec();
    for fact in &replay.effect_facts {
        if !replay_available.contains(fact.proposition()) {
            replay_available.push(fact.proposition().clone());
        }
    }
    for equation in crate::kernel::certified_store_equations(&replay.effect_facts) {
        if !replay_available.contains(&equation) {
            replay_available.push(equation);
        }
    }
    let mut unfolds = replay.unfolded_predicates.clone();
    unfolds.retain(|name| predicate_environment.get(name).is_some());
    let try_closer = |closers: Vec<ProofTactic>| -> Result<ProofCertificate, String> {
        let mut tactics = unfolds
            .iter()
            .cloned()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(existence_tactics.iter().cloned());
        tactics.extend(closers);
        let surface_have = ProofHave {
            proposition: surface_goal.clone(),
            proof: SourceProof::Script(tactics),
        };
        let surface_tactics = vec![
            ProofTactic::Have(surface_have.clone()),
            ProofTactic::Assumption,
        ];
        let certificate = ProofCertificate::from_proof_tactics(&surface_tactics)
            .map_err(|error| format!("produced an invalid certificate: {error:?}"))?;
        let replayed_goal = prove_have_at_point(
            &surface_have,
            theorem_environment,
            claim_label,
            tactic_index,
            &replay_available,
            &replay.effect_facts,
            parameters,
            arguments,
            pre_state,
            post_state,
            Some(result),
            &replay.program_point_states,
            Some(&replay.surface_propositions),
            predicate_environment,
            click_function_environment,
            function_requires,
            Some(path_index),
        )
        .map_err(|error| error.message().to_string())?;
        // `assumption` closes the claim by an exact match against the fact
        // the have just recorded, so the two must agree. The claim goal may
        // be spelled with `unfold(...)` active while the replay produces the
        // folded predicate; both name one proposition by the predicate's
        // definition.
        let replayed_matches = replayed_goal == *goal
            || (!unfolds.is_empty()
                && unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolds,
                    &replayed_goal,
                    &assumptions_from_propositions(&replay_available),
                )
                .as_ref()
                    == Ok(goal));
        if replayed_matches {
            Ok(certificate)
        } else {
            Err(format!(
                "proved a different proposition than the claim goal: {replayed_goal:?}"
            ))
        }
    };
    let mut last_error = None;
    for closer in [ProofTactic::Assumption, ProofTactic::Normalize] {
        match try_closer(vec![closer]) {
            Ok(certificate) => return Ok(certificate),
            Err(message) => last_error = Some(message),
        }
    }
    // A choice introduces a proof-local name that outcome lowering cannot
    // spell outside the replay scope; the ordinary `assumption` attempt above
    // handles the supported choose-and-witness shape directly. Witness-only
    // goals have no such name: instantiate both representations and lower the
    // remaining proposition through the same explicit certificate planner as
    // every other post-execution `simp`.
    if existence_tactics
        .iter()
        .all(|tactic| matches!(tactic, ProofTactic::Witness(_)))
    {
        let parameter_values = parameter_values(parameters, arguments)
            .map_err(|error| ClickError::new(error.message))?;
        let array_refs =
            array_refs_for_parameters(parameters, &parameter_values, post_state.memory());
        let (values, array_refs) =
            contract_environment_at_state(&parameter_values, &array_refs, post_state);
        let mut instantiated_goal = goal.clone();
        let mut instantiated_surface = if unfolds.is_empty() {
            surface_goal.clone()
        } else {
            unfold_structural_invariant_proposition(predicate_environment, surface_goal, &unfolds)
                .map_err(ClickError::new)?
        };
        for (index, tactic) in existence_tactics.iter().enumerate() {
            let ProofTactic::Witness(witness) = tactic else {
                unreachable!();
            };
            instantiated_goal = unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                &unfolds,
                &instantiated_goal,
                &assumptions_from_propositions(&replay_available),
            )
            .map_err(ClickError::new)?;
            let witness_value = evaluate_witness_tactic_value(
                witness,
                claim_label,
                path_index,
                index,
                &values,
                &array_refs,
                pre_state,
                post_state,
                Some(result),
                &assumptions_from_propositions(&replay_available),
                predicate_environment,
                click_function_environment,
                &replay.program_point_states,
            )?;
            instantiated_goal = apply_witness_tactic(
                witness,
                witness_value,
                instantiated_goal,
                claim_label,
                path_index,
                index,
            )?;
            if !matches!(instantiated_surface, ClickProposition::Exists { .. }) {
                instantiated_surface = synthesize_surface_proposition(
                    &unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        &unfolds,
                        goal,
                        &assumptions_from_propositions(&replay_available),
                    )
                    .map_err(ClickError::new)?,
                    parameters,
                    arguments,
                    post_state,
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}, tactic {tactic_index}: existential `simp` could not synthesize an explicit witness goal"
                    ))
                })?;
            }
            let ClickProposition::Exists { name, body, .. } = instantiated_surface else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}, tactic {tactic_index}: existential `simp` could not expose witness `{}` in its surface goal",
                    witness.name,
                )));
            };
            instantiated_surface = crate::lang::click::lowering::substitute_click_proposition(
                &body,
                &BTreeMap::from([(name, witness.value.clone())]),
            )
            .map_err(ClickError::new)?;
        }
        match lower_outcome_simp_proof(
            replay,
            &instantiated_surface,
            &instantiated_goal,
            &replay_available,
            parameters,
            arguments,
            pre_state,
            post_state,
            result,
            predicate_environment,
            click_function_environment,
        ) {
            Ok(SourceProof::Script(tactics)) => match try_closer(tactics) {
                Ok(certificate) => return Ok(certificate),
                Err(message) => last_error = Some(message),
            },
            Ok(_) => last_error = Some("explicit existential closer was not a script".to_string()),
            Err(error) => last_error = Some(error.message().to_string()),
        }
    }
    Err(ClickError::new(format!(
        "`{claim_label}` path {path_index}, tactic {tactic_index}: existential `simp` certificate failed replay: {}",
        last_error.unwrap_or_else(|| "no closer candidate applied".to_string())
    )))
}

pub(super) struct GroupedOutcomeSimpGoal {
    pub(super) claim_index: usize,
    pub(super) claim_label: String,
    pub(super) surface_goal: ClickProposition,
    pub(super) goal: Proposition,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn certify_grouped_outcome_simp_transition(
    replay: &TacticReplayState,
    goals: Vec<GroupedOutcomeSimpGoal>,
    claim_count: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_requires: &[Requirement],
    proof_label: &str,
    tactic_index: usize,
    path_index: usize,
) -> Result<ProofCertificate, ClickError> {
    let mut replay = replay.clone();
    let mut available = available.to_vec();
    let mut pending = goals;
    let mut tactics = Vec::new();
    let mut last_errors = BTreeMap::new();

    while !pending.is_empty() {
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for goal in pending {
            match certify_outcome_simp_have(
                &replay,
                &goal.surface_goal,
                &goal.goal,
                &available,
                parameters,
                arguments,
                pre_state,
                post_state,
                result,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                function_requires,
                &goal.claim_label,
                tactic_index,
                path_index,
            ) {
                Ok(surface_haves) => {
                    replay
                        .surface_propositions
                        .record_lowering(&goal.surface_goal, &goal.goal)?;
                    available.push(goal.goal);
                    tactics.extend(surface_haves);
                    made_progress = true;
                }
                Err(error) => {
                    last_errors.insert(goal.claim_index, error.message().to_string());
                    next_pending.push(goal);
                }
            }
        }
        if !made_progress {
            let details = next_pending
                .iter()
                .map(|goal| {
                    format!(
                        "claim {} (`{}`): {}",
                        goal.claim_index,
                        goal.claim_label,
                        last_errors
                            .get(&goal.claim_index)
                            .map(String::as_str)
                            .unwrap_or("no certificate was produced")
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            return Err(ClickError::new(format!(
                "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped `simp` could not certify its complete claim transition\n{details}"
            )));
        }
        pending = next_pending;
    }

    tactics.extend(std::iter::repeat_n(ProofTactic::Assumption, claim_count));
    ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
        ClickError::new(format!(
            "`{proof_label}` path {path_index}, tactic {tactic_index}: grouped `simp` produced an invalid transition certificate: {error:?}"
        ))
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn frame_certified_ensure_goals(
    claims: &[FunctionClaimRef<'_>],
    path_execution_facts: &[ExecutionPureFact],
    path_requirements: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    program_point_states: &ProgramPointStates,
    unfolded_predicates: &[String],
) -> Vec<(usize, Proposition)> {
    let mut reasoning_facts = path_requirements.to_vec();
    reasoning_facts.extend(
        path_execution_facts
            .iter()
            .filter(|fact| {
                matches!(
                    fact.proposition(),
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapLifetimeRetired { .. }
                )
            })
            .map(|fact| fact.proposition().clone()),
    );
    let assumptions = assumptions_from_propositions(&reasoning_facts);
    claims
        .iter()
        .enumerate()
        .filter_map(|(claim_index, claim)| {
            let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
                return None;
            };
            let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
                return None;
            };
            let goal = lower_ensure_proposition_goal(
                path_requirements,
                surface_goal,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                program_point_states,
                unfolded_predicates,
            )
            .ok()?;
            plan_simp_certificate(&goal, &assumptions)
                .is_some()
                .then_some((claim_index, goal))
        })
        .collect()
}

pub(super) fn comparison_program_point_variants(
    proposition: &ClickProposition,
    points: &[ProgramPointRef],
) -> Option<Vec<ClickProposition>> {
    if let ClickProposition::Not(body) = proposition {
        return Some(
            comparison_program_point_variants(body, points)?
                .into_iter()
                .map(|variant| ClickProposition::Not(Box::new(variant)))
                .collect(),
        );
    }
    if let ClickProposition::ForAll { c_type, name, body } = proposition {
        return Some(
            comparison_program_point_variants(body, points)?
                .into_iter()
                .map(|body| ClickProposition::ForAll {
                    c_type: *c_type,
                    name: name.clone(),
                    body: Box::new(body),
                })
                .collect(),
        );
    }
    if let ClickProposition::Implies(left, right) = proposition {
        let mut variants = comparison_program_point_variants(right, points)?
            .into_iter()
            .map(|right| ClickProposition::Implies(left.clone(), Box::new(right)))
            .collect::<Vec<_>>();
        if let Some(left_variants) = comparison_program_point_variants(left, points) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::Implies(Box::new(left), right.clone())),
            );
        }
        return Some(variants);
    }
    if let ClickProposition::Or(left, right) = proposition {
        let left_variants = comparison_program_point_variants(left, points)?;
        let right_variants = comparison_program_point_variants(right, points)?;
        let mut variants = vec![proposition.clone()];
        let mut push = |left: ClickProposition, right: ClickProposition| {
            let candidate = ClickProposition::Or(Box::new(left), Box::new(right));
            if !variants.contains(&candidate) {
                variants.push(candidate);
            }
        };
        for left in &left_variants {
            push(left.clone(), right.as_ref().clone());
        }
        for right in &right_variants {
            push(left.as_ref().clone(), right.clone());
        }
        for (left, right) in left_variants.into_iter().zip(right_variants) {
            push(left, right);
        }
        return Some(variants);
    }
    if let ClickProposition::And(left, right) = proposition {
        let mut variants = Vec::new();
        if let Some(right_variants) = comparison_program_point_variants(right, points) {
            variants.extend(
                right_variants
                    .into_iter()
                    .map(|right| ClickProposition::And(left.clone(), Box::new(right))),
            );
        }
        if let Some(left_variants) = comparison_program_point_variants(left, points) {
            variants.extend(
                left_variants
                    .into_iter()
                    .map(|left| ClickProposition::And(Box::new(left), right.clone())),
            );
        }
        return (!variants.is_empty()).then_some(variants);
    }
    // A predicate call names its memory snapshot only through its array-ref
    // arguments, so the snapshot is selected by wrapping the arguments —
    // uniformly, the way the recorded-spelling search in
    // `checked_surface_fact_at_point` already does. Wrapping a value argument
    // is harmless: it evaluates to the same value at every point it is
    // spellable at, and a wrapping that does not lower is discarded by the
    // caller's `check`.
    if let ClickProposition::PredicateCall { name, arguments } = proposition {
        let call = |wrap: &dyn Fn(&ContractExpression) -> ContractExpression| {
            ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments.iter().map(wrap).collect(),
            }
        };
        let mut variants = vec![proposition.clone()];
        if !arguments
            .iter()
            .any(|argument| matches!(argument, ContractExpression::Old(_)))
        {
            variants.push(call(&|argument| {
                ContractExpression::Old(Box::new(argument.clone()))
            }));
        }
        for point in points.iter().rev() {
            let candidate = call(&|argument| ContractExpression::At {
                selector: VisitSelector::ProgramPoint(point.clone()),
                expression: Box::new(argument.clone()),
            });
            if !variants.contains(&candidate) {
                variants.push(candidate);
            }
        }
        return Some(variants);
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let at_point =
        |expression: &ContractExpression, point: &ProgramPointRef| ContractExpression::At {
            selector: VisitSelector::ProgramPoint(point.clone()),
            expression: Box::new(expression.clone()),
        };
    let comparison = |left, right| ClickProposition::Comparison {
        left,
        operator: *operator,
        right,
    };
    let old_left = (!matches!(left, ContractExpression::Old(_)))
        .then(|| ContractExpression::Old(Box::new(left.clone())));
    let old_right = (!matches!(right, ContractExpression::Old(_)))
        .then(|| ContractExpression::Old(Box::new(right.clone())));
    let point_pairs = points
        .iter()
        .rev()
        .map(|point| (at_point(left, point), at_point(right, point)))
        .collect::<Vec<_>>();
    let mut variants = Vec::new();
    let mut push = |left, right| {
        let candidate = comparison(left, right);
        if !variants.contains(&candidate) {
            variants.push(candidate);
        }
    };
    push(left.clone(), right.clone());
    if let Some(old_left) = &old_left {
        push(old_left.clone(), right.clone());
    }
    if let Some(old_right) = &old_right {
        push(left.clone(), old_right.clone());
    }
    if let (Some(old_left), Some(old_right)) = (&old_left, &old_right) {
        push(old_left.clone(), old_right.clone());
    }
    for (point_left, point_right) in &point_pairs {
        push(point_left.clone(), right.clone());
        push(left.clone(), point_right.clone());
        push(point_left.clone(), point_right.clone());
    }

    let mut left_variants = vec![left.clone()];
    let mut right_variants = vec![right.clone()];
    if let Some(old_left) = old_left {
        left_variants.push(old_left);
    }
    if let Some(old_right) = old_right {
        right_variants.push(old_right);
    }
    for (point_left, point_right) in point_pairs {
        left_variants.push(point_left);
        right_variants.push(point_right);
    }
    for left in left_variants {
        for right in &right_variants {
            push(left.clone(), right.clone());
        }
    }
    Some(variants)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_surface_candidate_at_point(
    replay: &TacticReplayState,
    candidate: &ClickProposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let assumptions = assumptions_from_propositions(available);
    lower_surface_candidate_at_point_with_assumptions(
        replay,
        candidate,
        &assumptions,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_surface_candidate_at_point_with_assumptions(
    replay: &TacticReplayState,
    candidate: &ClickProposition,
    assumptions: &PureFactContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    check_verification_deadline()?;
    let values = parameter_values(parameters, arguments)?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (mut values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    let assumptions = assumptions.clone().allow_symbolic_contract_loads();
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        replay.old_reference_state(state),
        state,
        None,
        &assumptions,
        candidate,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &replay.program_point_states,
        &mut active_functions,
    )
    .map_err(ClickError::new)
}

pub(super) fn contract_expression_mentions_c_local(
    expression: &ContractExpression,
    parameter_names: &BTreeSet<&str>,
) -> bool {
    match expression {
        ContractExpression::CBinding(_) | ContractExpression::ResourceWildcard => false,
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => arguments
                .iter()
                .any(|argument| contract_expression_mentions_c_local(argument, parameter_names)),
            _ => false,
        },
        ContractExpression::CFragment(CExpression::Variable(name)) => {
            !parameter_names.contains(name.as_str())
        }
        ContractExpression::CFragment(_) => false,
        ContractExpression::Field { base, .. }
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::BitwiseNot(base) => {
            contract_expression_mentions_c_local(base, parameter_names)
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            contract_expression_mentions_c_local(left, parameter_names)
                || contract_expression_mentions_c_local(right, parameter_names)
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            contract_expression_mentions_c_local(then_branch, parameter_names)
                || contract_expression_mentions_c_local(else_branch, parameter_names)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contract_expression_mentions_c_local(start, parameter_names)
                || contract_expression_mentions_c_local(end, parameter_names)
                || contract_expression_mentions_c_local(initial, parameter_names)
                || contract_expression_mentions_c_local(body, parameter_names)
        }
        ContractExpression::Let { value, body, .. } => {
            contract_expression_mentions_c_local(value, parameter_names)
                || contract_expression_mentions_c_local(body, parameter_names)
        }
        ContractExpression::Call { arguments, .. } => arguments
            .iter()
            .any(|argument| contract_expression_mentions_c_local(argument, parameter_names)),
    }
}

pub(super) fn public_local_result_surface(
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
) -> bool {
    let parameter_names = parameters
        .iter()
        .map(syntax::C0Parameter::name)
        .collect::<BTreeSet<_>>();
    matches!(
        proposition,
        ClickProposition::Comparison { left, right, .. }
            if contract_expression_mentions_c_local(left, &parameter_names)
                || contract_expression_mentions_c_local(right, &parameter_names)
    )
}
