use super::*;

pub(super) struct TheoremApplicationContext<'a> {
    pub(super) values: &'a BTreeMap<String, CValue>,
    pub(super) array_refs: &'a ClickArrayRefs,
    pub(super) pre_state: &'a CState,
    pub(super) post_state: &'a CState,
    pub(super) result: Option<&'a CValue>,
    pub(super) recorded_snapshots: &'a RecordedSnapshots,
}

pub(super) fn apply_theorem_applications_to_available(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    available: Vec<Proposition>,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    apply_theorem_applications_to_available_with_lowering_context(
        theorem_environment,
        theorem_applications,
        claim_label,
        path_index,
        available,
        None,
        context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn apply_theorem_applications_to_available_with_lowering_context(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    mut available: Vec<Proposition>,
    lowering_context: Option<&[Proposition]>,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    for (tactic_index, application) in theorem_applications {
        available = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &available,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, *tactic_index, message)
        })?;
        let mut lowering_available = lowering_context.unwrap_or(&available).to_vec();
        for fact in &available {
            if !lowering_available.contains(fact) {
                lowering_available.push(fact.clone());
            }
        }
        let conclusions = instantiate_theorem_application(
            theorem_environment,
            application,
            claim_label,
            path_index,
            *tactic_index,
            &available,
            &lowering_available,
            context,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )?;
        for conclusion in conclusions {
            if !available.contains(&conclusion) {
                available.push(conclusion);
            }
        }
    }
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &available,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, 0, message))
}

fn instantiate_theorem_application(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    available: &[Proposition],
    lowering_available: &[Proposition],
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let assumptions = assumptions_from_propositions(available);
    let lowering_assumptions = assumptions_from_propositions(lowering_available);
    instantiate_theorem_application_with_assumptions(
        theorem_environment,
        application,
        claim_label,
        path_index,
        tactic_index,
        available,
        &assumptions,
        &lowering_assumptions,
        context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )
}

/// Instantiates one theorem from an explicit evidence set while borrowing the
/// already-indexed contexts used to unfold requirements and lower arguments.
///
/// `available` is the complete admissible evidence set: ambient facts in the
/// assumption contexts can affect representation and evaluation, but cannot
/// discharge an omitted theorem requirement.
#[allow(clippy::too_many_arguments)]
pub(super) fn instantiate_theorem_application_with_assumptions(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    available: &[Proposition],
    assumptions: &PureFactContext,
    lowering_assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            format!("unknown theorem `{}`", application.name),
        )
    })?;
    if application.arguments.len() != theorem.parameters().len() {
        return Err(theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            format!(
                "theorem `{}` expects {} argument(s), got {}",
                theorem.name(),
                theorem.parameters().len(),
                application.arguments.len()
            ),
        ));
    }

    let (values, array_refs, algebraic_values) = theorem_application_bindings(
        theorem,
        application,
        context,
        lowering_assumptions,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, tactic_index, message))?;
    // A theorem's clauses are lowered at the application's state exactly as
    // any proof-side proposition is: elaborated with the theorem's
    // parameters bound and lowered by the kernel.
    // The theorem's parameters shadow any C local of the same name: the
    // application binds them, not the state.
    let bind = |state: &CState| {
        values.iter().fold(state.clone(), |state, (name, value)| {
            state.with_local(name.clone(), value.clone())
        })
    };
    let pre_state = bind(context.pre_state);
    let post_state = bind(context.post_state);
    let lower = |proposition: &ClickProposition| {
        lower_fixed_state_proposition_through_kernel_with_algebraic_values(
            proposition,
            lowering_assumptions,
            &values,
            &array_refs,
            &algebraic_values,
            &pre_state,
            &post_state,
            None,
            context.recorded_snapshots,
            predicate_environment,
            click_function_environment,
        )
    };

    for requirement in theorem.requires() {
        let Some(requirement) = requirement.proposition() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "theorem `{}` has a non-proposition requirement that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let mut lowered = lower(requirement).map_err(|error| {
            theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "could not lower theorem `{}` requirement: {error}",
                    theorem.name()
                ),
            )
        })?;
        lowered = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &lowered,
            assumptions,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, tactic_index, message)
        })?;
        lowered = lowered.clone();
        if !available.iter().any(|fact| {
            let fact = fact.clone();
            fact == lowered || condition_polarity_equivalent(&fact, &lowered)
        }) && !matches!(normalize_proposition(&lowered), SimpProposition::True)
        {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "required exact fact for theorem `{}` is unavailable: {}",
                    theorem.name(),
                    describe_missing_pure_fact(&lowered, available, &[], &[], &[], &[])
                ),
            ));
        }
    }

    let mut conclusions = Vec::new();
    for ensure in theorem.ensures() {
        let Ensure::Proposition(conclusion) = ensure.ensure() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "theorem `{}` has a non-proposition conclusion that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let conclusion = lower(conclusion).map_err(|error| {
            theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "could not lower theorem `{}` conclusion: {}",
                    theorem.name(),
                    error
                ),
            )
        })?;
        conclusions.push(conclusion.clone());
    }
    Ok(conclusions)
}

pub(super) fn theorem_application_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<
    (
        BTreeMap<String, CValue>,
        ClickArrayRefs,
        BTreeMap<String, SpecAlgebraicExpression>,
    ),
    String,
> {
    let mut active_functions = BTreeSet::new();
    let mut values = BTreeMap::new();
    let mut array_refs = BTreeMap::new();
    let mut algebraic_values = BTreeMap::new();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        let Some(parameter_type) = parameter.click_type().c_type() else {
            let ClickType::Algebraic(expected_type) = parameter.click_type() else {
                unreachable!("Click theorem parameters are C or algebraic values")
            };
            let value = capture_fixed_state_algebraic_expression(
                argument,
                assumptions,
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                context.recorded_snapshots,
                predicate_environment,
                click_function_environment,
            )?;
            let type_matches = value.algebraic_type.name == expected_type.name
                && value.algebraic_type.arguments.len() == expected_type.arguments.len()
                && expected_type
                    .arguments
                    .iter()
                    .zip(&value.algebraic_type.arguments)
                    .all(|(expected, actual)| {
                        matches!(expected, ClickType::C(expected) if expected.to_kernel_type() == *actual)
                    });
            if !type_matches {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects algebraic type `{}`, got `{}`",
                    theorem.name(),
                    parameter.name(),
                    expected_type.name,
                    value.algebraic_type.name
                ));
            }
            algebraic_values.insert(parameter.name().to_string(), value);
            continue;
        };
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_fixed_state_array_ref_through_kernel(
                argument,
                assumptions,
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                context.recorded_snapshots,
                predicate_environment,
                click_function_environment,
            )?;
            let expected_element_type =
                click_array_element_type(parameter_type).ok_or_else(|| {
                    format!(
                        "theorem `{}` parameter `{}` is not an array-ref parameter",
                        theorem.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    theorem.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            values.insert(
                parameter.name().to_string(),
                CValue::typed_pointer(
                    array_ref.pointer.clone(),
                    expected_element_type.pointer_to().unwrap(),
                ),
            );
            array_refs.insert(parameter.name().to_string(), array_ref);
        } else {
            let value = evaluate_contract_expression_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                context.recorded_snapshots,
                &mut active_functions,
            )?;
            if !c_value_matches_click_type(&value, parameter_type) {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {}, got {value:?}",
                    theorem.name(),
                    parameter.name(),
                    describe_c0_type(parameter_type)
                ));
            }
            values.insert(parameter.name().to_string(), value);
        }
    }
    Ok((values, array_refs, algebraic_values))
}

fn theorem_application_error(
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    message: impl Into<String>,
) -> ClickError {
    let path = path_index
        .map(|index| format!(" path {index},"))
        .unwrap_or_default();
    ClickError::new(format!(
        "`{claim_label}`{path} tactic {tactic_index}: `apply` failed: {}",
        message.into()
    ))
}
