use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_surface_atomic_derivation(
    view: ExecutionView<'_>,
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
            "derivation lowering: conclusion form",
            || {
                checked_surface_fact_at_point(
                    view,
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
            view,
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
            view,
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
            view,
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
    let premise_synthesis_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: premise form",
    );
    let parameter_names = parameters
        .iter()
        .map(syntax::C0Parameter::name)
        .collect::<BTreeSet<_>>();
    // A premise written through load variables has no direct
    // surface form; resolving the internal names back to their load
    // forms through the defining equations recovers one.
    let defining_premises: Vec<Proposition> = available
        .iter()
        .filter(|premise| crate::kernel::is_load_variable_defining_fact(premise))
        .cloned()
        .collect();
    for premise in derivation.context_premises() {
        let synthesize_premise = |premise: &Proposition| {
            if derivation.has_typed_atomic_evidence() {
                checked_surface_comparison_fact_for_typed_derivation(
                    view,
                    premise,
                    SurfaceFactMatch::AvailabilityEquivalent,
                    available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
            } else {
                checked_surface_comparison_fact_at_point(
                    view,
                    premise,
                    SurfaceFactMatch::AvailabilityEquivalent,
                    available,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                )
            }
        };
        match synthesize_premise(&premise).or_else(|error| {
            let resolved = crate::kernel::resolve_load_variables_via(&premise, &defining_premises);
            let resolved = if resolved == premise {
                crate::kernel::resolve_load_variables_from_registry(&premise)
            } else {
                resolved
            };
            if resolved == premise {
                return Err(error);
            }
            synthesize_premise(&resolved)
        }) {
            Ok(surface) => {
                let surface = match anchor_point {
                    // Requirement-definedness facts are recorded when the
                    // function context is built. Re-elaborating their
                    // parameter-only expression after resources have been
                    // folded can produce `false`, even though the exact
                    // certified entry fact and its form remain
                    // available. Keep that stable form so fresh view
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
                        ) && view
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
    drop(premise_synthesis_span);
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
        view.old_reference_state(state),
        state,
        None,
        &view.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .map_err(ClickError::new)?;
    // `normalize()` must also survive a fresh source view. The full
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
        view.old_reference_state(state),
        state,
        None,
        &view.program_point_states,
        predicate_environment,
        click_function_environment,
    )
    .is_ok_and(|goal| normalizes_context_free(&goal));
    drop(_normalization_span);
    let availability_kind = |pairs: &[(Proposition, ClickProposition)]| {
        let surface_premises = pairs
            .iter()
            .map(|(_, surface)| {
                view.surface_propositions
                    .available_kernel(surface, available)
                    .cloned()
                    .map(Ok)
                    .unwrap_or_else(|| {
                        lower_point_proposition(
                            surface,
                            available,
                            parameters,
                            arguments,
                            view.old_reference_state(state),
                            state,
                            None,
                            &view.program_point_states,
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
            "derivation lowering: view derivation check",
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
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| plan_recorded_signed_order_path(&lowered_conclusion, pairs));
    let typed_equality_pairs = recorded_bitvector_equality_pairs(derivation, &premise_pairs);
    let typed_equality_plan = typed_equality_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_bitvector_equality_path(&lowered_conclusion, derivation, pairs)
        });
    let typed_equality_rewrite_paths =
        recorded_bitvector_equality_rewrite_path_pairs(derivation, &premise_pairs);
    let typed_equality_rewrite_plan = typed_equality_rewrite_paths
        .as_ref()
        .filter(|paths| {
            availability_kind(&paths.iter().flatten().cloned().collect::<Vec<_>>()).is_some()
        })
        .and_then(|paths| {
            plan_recorded_bitvector_equality_rewrite_paths(&lowered_conclusion, derivation, paths)
        });
    let typed_increment_pairs =
        recorded_int32_increment_upper_bound_pairs(derivation, &premise_pairs);
    let typed_increment_plan = typed_increment_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_upper_bound_for_context(&lowered_conclusion, pairs, false)
        });
    let typed_increment_constant_upper_pairs =
        recorded_int32_increment_constant_upper_bound_pairs(derivation, &premise_pairs);
    let typed_increment_constant_upper_plan = typed_increment_constant_upper_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_increment_lower_bound_for_context(&lowered_conclusion, pairs, false)
        });
    let typed_increment_greater_equal_pairs =
        recorded_int32_increment_greater_equal_lower_bound_pairs(derivation, &premise_pairs);
    let typed_increment_greater_equal_plan = typed_increment_greater_equal_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_one_le_predecessor_for_context(&lowered_conclusion, pairs, false)
        });
    let typed_equal_one_predecessor_pairs =
        recorded_int32_equal_one_predecessor_is_nonnegative_pairs(derivation, &premise_pairs)
            .or_else(|| {
                recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
                    derivation,
                    &premise_pairs,
                )
            });
    let typed_equal_one_predecessor_plan = typed_equal_one_predecessor_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_equal_one_predecessor_for_context(
                &lowered_conclusion,
                derivation,
                pairs,
                false,
            )
        });
    let typed_equal_one_predecessor_zero_pairs =
        recorded_int32_equal_one_predecessor_is_zero_pairs(derivation, &premise_pairs);
    let typed_equal_one_predecessor_zero_plan = typed_equal_one_predecessor_zero_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_equal_one_predecessor_is_zero(
                &lowered_conclusion,
                derivation,
                pairs,
            )
        });
    let typed_le_not_lt_equality_pairs =
        recorded_int32_le_and_not_lt_implies_equality_pairs(derivation, &premise_pairs);
    let typed_le_not_lt_equality_plan = typed_le_not_lt_equality_pairs
        .as_ref()
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
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
        .filter(|pairs| availability_kind(pairs).is_some())
        .and_then(|pairs| {
            plan_recorded_int32_le_and_neq_implies_strict_for_context(
                &lowered_conclusion,
                pairs,
                false,
            )
        });
    let typed_path_written = typed_order_plan.is_some()
        || typed_equality_plan.is_some()
        || typed_equality_rewrite_plan.is_some()
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
        || typed_equal_one_predecessor_plan.is_some()
        || typed_equal_one_predecessor_zero_plan.is_some()
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
    } else if typed_equality_rewrite_plan.is_some() {
        premise_pairs = typed_equality_rewrite_paths
            .expect("a typed equality-rewrite plan retains its exact path premises")
            .into_iter()
            .flatten()
            .collect();
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
    } else if typed_equal_one_predecessor_plan.is_some() {
        premise_pairs = typed_equal_one_predecessor_pairs
            .expect("a typed equal-one predecessor plan retains its exact equality path");
    } else if typed_equal_one_predecessor_zero_plan.is_some() {
        premise_pairs = typed_equal_one_predecessor_zero_pairs
            .expect("a typed predecessor-zero plan retains its exact equality path");
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
        && !typed_path_written
        && (premise_pairs.is_empty() || availability_kind(&premise_pairs).is_none())
    {
        return Err(ClickError::new(format!(
            "surface premises do not view the atomic derivation of {}\nunexpressed derivation premises: {}",
            describe_pure_fact(&lowered_conclusion, parameters, arguments),
            describe_unexpressed_pure_facts(&unexpressed_premises, parameters, arguments,),
        )));
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
    if let Some(tactics) = typed_equality_rewrite_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded bitvector equality-rewrite paths produced a non-simple expansion: {error:?}"
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
    if let Some(tactics) = typed_equal_one_predecessor_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded equal-one predecessor rule produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
    if let Some(tactics) = typed_equal_one_predecessor_zero_plan {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded predecessor-zero rule produced a non-simple expansion: {error:?}"
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
    // premise is usable only when the surface form lowers at view to
    // the same kernel equality the plan rewrote with. A snapshot-bridged
    // form (the same fact recorded against an earlier memory) denotes
    // the value only through frame reasoning, which the simple rewrite
    // cannot check; those premises stay available to the transport path.
    let surface_matches_kernel = |kernel: &Proposition, surface: &ClickProposition| {
        view.surface_propositions
            .available_kernel(surface, available)
            .cloned()
            .map(Ok)
            .unwrap_or_else(|| {
                lower_point_proposition(
                    surface,
                    available,
                    parameters,
                    arguments,
                    view.old_reference_state(state),
                    state,
                    None,
                    &view.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
            })
            .is_ok_and(|lowered| &lowered == kernel)
    };
    let rewrite_pairs = premise_pairs
        .iter()
        .filter(|(kernel, surface)| surface_matches_kernel(kernel, surface))
        .cloned()
        .collect::<Vec<_>>();
    // The premises the planner selected are already written and validated;
    // when they suffice to write the rewrite chain, the ambient harvest
    // below never runs. Attributed measurement showed that harvest form
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
    // These planners consume only the derivation-selected premise pairs.
    // Try them before any compatibility-era equality recovery so a typed
    // named rule or structural universal never pays for an ambient harvest.
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
        &view.effect_facts,
        state,
    ) {
        ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "universal goal discharge produced a non-simple expansion: {error:?}"
            ))
        })?;
        return Ok((conclusion, SourceProof::Script(tactics)));
    }
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
    let _transport_span = crate::instrumentation::OperationTiming::new(
        "have",
        "atomic derivation lowering",
        "derivation lowering: fact transport planning",
    );
    let transport_recognition = assumptions_from_propositions(available);
    for (_, surface_source) in &premise_pairs {
        let source = view
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
                    view.old_reference_state(state),
                    state,
                    None,
                    &view.program_point_states,
                    predicate_environment,
                    click_function_environment,
                )
            });
        let Ok(source) = source else {
            continue;
        };
        if !(source == lowered_conclusion
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
            &view.effect_facts,
            parameters,
            arguments,
            view,
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
        "smart reasoning found a derivation, but Click has no explicit simple certificate for {}\n  selected premises: {}\n  checkable equality rewrites: {}{}",
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

fn plan_explicit_increment_lower_bound_transport(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    // A named local or post-store field bound can be proved at the latest
    // retained program point and then transported to the requested surface
    // form. Keep those two proof steps explicit: the arithmetic theorem
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
    let (goal_lower, _) = signed_nonstrict_parts(goal)?;
    for (lower_kernel, lower_surface) in premise_pairs {
        let Some((lower, base)) = signed_nonstrict_parts(lower_kernel) else {
            continue;
        };
        if lower != goal_lower {
            continue;
        }
        let Some((surface_lower, surface_base)) = surface_nonstrict_parts(lower_surface) else {
            continue;
        };
        for (upper_kernel, upper_surface) in premise_pairs {
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
                    proof: SourceProof::Script(vec![ProofTactic::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_increment_lower_bound".to_string(),
                            arguments: vec![surface_base, surface_lower, surface_upper],
                        },
                        premises: vec![lower_surface.clone(), upper_surface.clone()],
                    }]),
                }),
                ProofTactic::TransportUsing {
                    source: intermediate_surface.clone(),
                    target: surface_goal.clone(),
                    premises: vec![intermediate_surface],
                },
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

    let tactics =
        plan_explicit_increment_lower_bound_transport(&kernel_goal, &goal, &premise_pairs).expect(
            "source-site annotation on the constant must not hide the increment certificate",
        );
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Have(ProofHave {
                    proof: SourceProof::Script(body),
                    ..
                }),
                ProofTactic::TransportUsing { .. }
            ] if matches!(body.as_slice(), [ProofTactic::ApplyTheoremUsing { .. }])
        ),
        "point-closing theorem and transport steps must not retain dead assumptions: {tactics:?}"
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
/// after its guards discharge from the remaining listed premises. The named
/// `instantiate ... using` step adds the specialized fact and `assumption`
/// closes the exact goal, matching independent proof-step check.
pub(super) fn plan_explicit_forall_instantiation(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
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
            // match the goal by exactly the equivalence assumption checks.
            if conclusion != *goal {
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
/// (and implication antecedent), then specialize one listed universal premise
/// at the introduced binder. Instantiation adds the specialized fact; an
/// optional transport adds its target, and `assumption` closes the exact goal.
/// The instantiated guards discharge from the introduced antecedent plus the
/// remaining listed premises.
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
    let closes_by_assumption =
        conclusion == *goal_conclusion || conclusion.clone() == goal_conclusion.clone();
    // Constant-argument instances offer several instantiation candidates, so
    // the caller may insist the instantiated conclusion provably reaches the
    // goal before accepting a transport that check would reject.
    if !closes_by_assumption
        && let Some(gate) = conclusion_gate
        && !gate(&conclusion)
    {
        return None;
    }
    // A residual form difference (for example a loop counter the listed
    // order facts pin to a constant) crosses through an explicit transport
    // from the instantiated conclusion instead. The transported closure is
    // validated by the caller's immediate certificate validation, so no weaker
    // equivalence pre-check runs here.
    let transport_closure = if closes_by_assumption {
        None
    } else {
        // A loop-exit universal invariant fact is written through an
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

pub(super) fn plan_explicit_forall_goal_from_premises(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
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
    None
}

fn plan_explicit_forall_goal(
    goal: &Proposition,
    surface_goal: &ClickProposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    effect_facts: &[ExecutionPureFact],
    post_state: &CState,
) -> Option<Vec<ProofTactic>> {
    if let Some(tactics) =
        plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)
    {
        return Some(tactics);
    }
    let Proposition::ForAll {
        body: goal_body, ..
    } = goal
    else {
        return None;
    };
    let ClickProposition::ForAll {
        body: surface_body, ..
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
    // transport consumes atomic premises; write conjunction elimination
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
    let checks = |selected: &[(Proposition, ClickProposition)]| {
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
    if !checks(&selected) {
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
            if checks(&selected) {
                break;
            }
        }
    }
    if !checks(&selected) {
        return None;
    }
    let mut index = 0;
    while index < selected.len() {
        let mut reduced = selected.clone();
        reduced.remove(index);
        if checks(&reduced) {
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
    // The reflexive source normalizes context-free; the transport check
    // materializes its symbolic load term itself, so no nested `have` is
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
            if !pure_fact_is_available(goal, &available) {
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
            if derivation.conclusion() != goal || !derivation.check(&assumptions) {
                return Err(ClickError::new(
                    "`simp() using` selected a derivation that does not check from exactly its listed premises",
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
        // `left`/`right` check accepts the selected disjunct when it is the
        // same total boolean condition as an available fact up to polarity
        // (e.g. `x > 0` from `not (x <= 0)`); construction mirrors exactly
        // that check rather than demanding the literal form.
        let disjunct_available = pure_fact_is_available(child_goal, &available)
            || available
                .iter()
                .any(|fact| condition_polarity_equivalent(fact, child_goal));
        if child.conclusion() != child_goal || !disjunct_available {
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
        .or_else(|| plan_explicit_nonstrict_transitive(goal, premise_pairs))
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

pub(super) fn plan_explicit_loadability_transport(
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

pub(super) fn recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .int32_equal_one_predecessor_is_nonnegative_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
}

pub(super) fn recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .int32_equal_one_predecessor_strictly_decreases_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
}

pub(super) fn recorded_int32_equal_one_predecessor_is_zero_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .int32_equal_one_predecessor_is_zero_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
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

pub(super) fn plan_recorded_int32_equal_one_predecessor_for_context(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
    point_application_closes_goal: bool,
) -> Option<Vec<ProofTactic>> {
    let path = derivation
        .int32_equal_one_predecessor_is_nonnegative_path()
        .or_else(|| derivation.int32_equal_one_predecessor_strictly_decreases_path())?;
    let value = one_le_predecessor_value(goal)?;
    let one_le_kernel = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(Bitvector32Term::Constant(1)),
            Box::new(value.clone()),
        ),
        true,
    );
    let first = path.first()?;
    let (_, first_surface) = premise_pairs
        .iter()
        .find(|(kernel, _)| kernel == first.premise())?;
    let first_oriented = orient_surface_bitvector_equality(first, first_surface)?;
    let one_le_surface = surface_one_le_equality_source(&first_oriented)?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = one_le_kernel.clone();
    let mut equality_tactics = Vec::with_capacity(path.len() + 1);
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
        equality_tactics.push(ProofTactic::Rewrite(oriented_surface));
    }
    if !normalizes_context_free(&current) {
        return None;
    }
    equality_tactics.push(ProofTactic::Normalize);

    let mut predecessor_tactics =
        plan_explicit_one_le_predecessor(goal, &[(one_le_kernel, one_le_surface.clone())])?;
    if point_application_closes_goal {
        remove_trailing_theorem_assumption(&mut predecessor_tactics)?;
        let ProofTactic::Have(positive) = predecessor_tactics.first_mut()? else {
            return None;
        };
        let SourceProof::Script(body) = &mut positive.proof else {
            return None;
        };
        remove_trailing_theorem_assumption(body)?;
    }
    let mut tactics = Vec::with_capacity(predecessor_tactics.len() + 1);
    tactics.push(ProofTactic::Have(ProofHave {
        proposition: one_le_surface,
        proof: SourceProof::Script(equality_tactics),
    }));
    tactics.append(&mut predecessor_tactics);
    Some(tactics)
}

pub(super) fn plan_recorded_int32_equal_one_predecessor_is_zero(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let path = derivation.int32_equal_one_predecessor_is_zero_path()?;
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

/// A theorem application can complete an exact matching proposition goal.
/// Outcome check can instead add an equivalent snapshot fact, so callers
/// specify whether the checked application closes this particular goal.
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

pub(super) fn remove_trailing_theorem_assumption(tactics: &mut Vec<ProofTactic>) -> Option<()> {
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

fn recorded_bitvector_equality_path_pairs(
    path: &[BitvectorEqualityDerivationStep],
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    path.iter()
        .map(|step| {
            premise_pairs
                .iter()
                .find(|(kernel, _)| kernel == step.premise())
                .cloned()
        })
        .collect()
}

fn recorded_bitvector_equality_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<(Proposition, ClickProposition)>> {
    derivation
        .bitvector_equality_path()
        .and_then(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
}

pub(super) fn recorded_bitvector_equality_rewrite_path_pairs(
    derivation: &PropositionDerivation,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<Vec<(Proposition, ClickProposition)>>> {
    derivation
        .bitvector_equality_rewrite_paths()?
        .iter()
        .map(|path| recorded_bitvector_equality_path_pairs(path, premise_pairs))
        .collect()
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

/// Transcribe the exact equality paths retained for variables occurring
/// inside a larger atomic goal. Each path is applied in kernel-selected order;
/// the rewritten proposition must then normalize without context.
pub(super) fn plan_recorded_bitvector_equality_rewrite_paths(
    goal: &Proposition,
    derivation: &PropositionDerivation,
    premise_paths: &[Vec<(Proposition, ClickProposition)>],
) -> Option<Vec<ProofTactic>> {
    let paths = derivation.bitvector_equality_rewrite_paths()?;
    if paths.len() != premise_paths.len() {
        return None;
    }
    let available = premise_paths
        .iter()
        .flatten()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let mut current = goal.clone();
    let mut tactics = Vec::new();
    for (path, pairs) in paths.iter().zip(premise_paths) {
        if path.len() != pairs.len() {
            return None;
        }
        for (step, (_, surface)) in path.iter().zip(pairs) {
            let oriented_surface = orient_surface_bitvector_equality(step, surface)?;
            let oriented_kernel = Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(step.source().clone()),
                    Box::new(step.target().clone()),
                ),
                true,
            );
            current = rewrite_proposition_by_exact_equality(&current, &oriented_kernel, &available)
                .ok()?;
            tactics.push(ProofTactic::Rewrite(oriented_surface));
        }
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
/// goal is written `<`; a reversed (`>`) goal needs the reversed-form rule.
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
/// [`goal_exact_less_than_parts`]. For a theorem whose conclusion is written
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

pub(super) fn surface_strict_parts(
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
/// contradiction. Check pushes each introduced antecedent exactly as the
/// goal writes it, so the refuting premise must be that form's exact
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
/// the consequent's surface form, so the checker revalidates the same bounded
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

/// `first <= middle` and `middle <= last` give `first <= last` through
/// `int32_le_transitive`; the non-strict counterpart of
/// [`plan_explicit_strict_transitive`].
fn plan_explicit_nonstrict_transitive(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
) -> Option<Vec<ProofTactic>> {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessEqual(goal_first, goal_last),
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
                        name: "int32_le_transitive".to_string(),
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
/// from a listed `x >= c2` (in either form) when `c1 <= c2`, through
/// `int32_ge_transitive` over the context-free constant order and the
/// reversed-form theorem.
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
/// `synthesize_missing_leg` is set, a nested `have` derives it from the same
/// premises with the explicit equality-rewrite search (closing by a listed
/// premise or context-free normalization), so the emitted certificate still
/// names every dependency. Only outcome contexts pass `synthesize_missing_leg`:
/// a pure theorem proof has no `have`, so its planner must not emit one.
fn plan_explicit_predecessor_upper_bound(
    goal: &Proposition,
    premise_pairs: &[(Proposition, ClickProposition)],
    synthesize_missing_leg: bool,
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
            if !synthesize_missing_leg {
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

fn one_le_predecessor_value(goal: &Proposition) -> Option<Bitvector32Term> {
    if let Some((goal_lower, predecessor)) = goal_exact_less_equal_parts(goal) {
        if goal_lower != &Bitvector32Term::Constant(0) {
            return None;
        }
        let Bitvector32Term::Subtract(value, amount) = predecessor else {
            return None;
        };
        (amount.as_ref() == &Bitvector32Term::Constant(1)).then(|| value.as_ref().clone())
    } else {
        let (predecessor, value) = goal_exact_less_than_parts(goal)?;
        let Bitvector32Term::Subtract(predecessor_value, amount) = predecessor else {
            return None;
        };
        (predecessor_value.as_ref() == value && amount.as_ref() == &Bitvector32Term::Constant(1))
            .then(|| value.clone())
    }
}

fn surface_one_le_equality_source(surface: &ClickProposition) -> Option<ClickProposition> {
    match surface {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_one_le_equality_source(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            ..
        } => Some(ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(1))),
            operator: ComparisonOperator::LessEqual,
            right: left.clone(),
        }),
        _ => None,
    }
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
    // form belongs to `int32_increment_greater_equal_lower_bound`, whose
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
                        | Proposition::CHeapAllocationFreed { .. }
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
    // uniformly, the way the recorded-form search in
    // `checked_surface_fact_at_point` already does. Wrapping a value argument
    // is harmless: it evaluates to the same value at every point it is
    // synthesizable at, and a wrapping that does not lower is discarded by the
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
    view: ExecutionView<'_>,
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
        view,
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
    view: ExecutionView<'_>,
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
        view.old_reference_state(state),
        state,
        None,
        &assumptions,
        candidate,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &view.program_point_states,
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
