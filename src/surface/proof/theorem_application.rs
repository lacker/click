use super::*;

pub(super) struct TheoremApplicationContext<'a> {
    pub(super) values: &'a BTreeMap<String, CValue>,
    pub(super) array_refs: &'a ClickArrayRefs,
    pub(super) pre_state: &'a CState,
    pub(super) post_state: &'a CState,
    pub(super) result: Option<&'a CValue>,
    pub(super) recorded_snapshots: &'a RecordedSnapshots,
    pub(super) integer_values:
        &'a crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    /// Physical pointee widths for C parameters in the caller's scope.  A
    /// theorem application may rename such a parameter, so the application
    /// binding maps this by argument expression before lowering the callee's
    /// propositions.
    pub(super) pointer_element_widths: BTreeMap<String, u32>,
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
    if is_integer_range_fold_theorem_name(&application.name) {
        return instantiate_integer_range_fold_theorem_application(
            application,
            claim_label,
            path_index,
            tactic_index,
            available,
            assumptions,
            context,
            predicate_environment,
            click_function_environment,
        );
    }
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            format!("unknown theorem `{}`", application.name),
        )
    })?;
    let theorem = resolve_generic_theorem_application(
        theorem,
        application,
        theorem_environment,
        lowering_assumptions,
        context,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, tactic_index, message))?;
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

    let (values, array_refs, algebraic_values, integer_values) = theorem_application_bindings(
        &theorem,
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
    let pointer_element_widths =
        theorem_application_pointer_element_widths(&theorem, application, context);
    let bound_array_memories =
        theorem_application_bound_array_memories(&theorem, application, &array_refs);
    let lower = |proposition: &ClickProposition| {
        lower_fixed_state_proposition_through_kernel_with_bound_array_memories(
            proposition,
            lowering_assumptions,
            &values,
            &array_refs,
            &algebraic_values,
            &integer_values,
            &bound_array_memories,
            &pre_state,
            &post_state,
            None,
            context.recorded_snapshots,
            predicate_environment,
            click_function_environment,
            &BTreeSet::new(),
            pointer_element_widths.clone(),
        )
    };

    for (requirement_index, requirement) in theorem.requires().iter().enumerate() {
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
        // A named `using` premise may be a checked conjunction, such as the
        // `defined(x + y)` fact emitted for a C addition.  The theorem may
        // require one of that fact's proper conjuncts (the no-overflow
        // condition), so select it through the same exact structural rule as
        // the kernel `extract` step.  This does not derive or normalize a
        // weaker proposition: the complete conjunction remains the supplied
        // evidence and only its checked conjunct satisfies this requirement.
        if !exact_fact_is_available(&lowered, available)
            && !matches!(normalize_proposition(&lowered), SimpProposition::True)
        {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                describe_unavailable_theorem_requirement(
                    theorem.name(),
                    requirement_index,
                    requirement,
                    &theorem
                        .parameters()
                        .iter()
                        .zip(&application.arguments)
                        .map(|(parameter, argument)| {
                            (
                                parameter.name().to_string(),
                                crate::surface::diagnostics::describe_contract_expression(argument),
                            )
                        })
                        .collect::<Vec<_>>(),
                    &lowered,
                ),
            ));
        }
        // A range premise states two things, and the theorem's own proof
        // assumed both: that `a..b` is a valid 32-bit byte extent, and that
        // those bytes are loadable. Applying it owes both, or a range that is
        // vacuously loadable because its extent wrapped would hand the theorem
        // the valid-extent fact it never established. The guards are spelled
        // over the element count, which is the spelling a proof can write.
        for guard in crate::kernel::stated_loadable_extent_guards(&lowered) {
            if exact_fact_is_available(&guard, available)
                || matches!(normalize_proposition(&guard), SimpProposition::True)
            {
                continue;
            }
            return Err(theorem_application_error(
                claim_label,
                path_index,
                tactic_index,
                format!(
                    "theorem `{}` requirement {requirement_index} states a memory range, so \
                     applying it needs that range to be a valid 32-bit byte extent here: `{}` is \
                     not an available fact. A range's extent is `(end - start) * width` in 32-bit \
                     arithmetic, and without that bound it can wrap to fewer bytes than its \
                     element count names",
                    theorem.name(),
                    crate::surface::proof::describe_pure_fact(&guard, &[], &[]),
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

/// The refusal for a theorem requirement the application cannot discharge.
///
/// A reader fixes this by supplying the missing premise, so the sentence has
/// to say which requirement is missing and what the application instantiated
/// it to. The kind alone (`int32 equality is true`) names neither: with more
/// than one requirement it does not even identify the clause, and an argument
/// naming another state (`old(a)`) instantiates the same source clause to a
/// different fact than the same clause at the current state. Print the source
/// clause as written, the arguments its own names were bound to, and then its
/// instantiation through the bounded proposition renderer, which spells both
/// sides.
pub(super) fn describe_unavailable_theorem_requirement(
    theorem_name: &str,
    requirement_index: usize,
    requirement: &ClickProposition,
    bindings: &[(String, String)],
    lowered: &Proposition,
) -> String {
    let mut referenced = BTreeSet::new();
    crate::surface::lowering::collect_click_proposition_referenced_names(
        requirement,
        &mut referenced,
    );
    let bound = bindings
        .iter()
        .filter(|(parameter, _)| referenced.contains(parameter))
        .map(|(parameter, argument)| format!("{parameter} = {argument}"))
        .collect::<Vec<_>>();
    let bound = if bound.is_empty() {
        String::new()
    } else {
        format!(" with {}", bound.join(", "))
    };
    format!(
        "required exact fact for theorem `{theorem_name}` is unavailable: requirement {} `{}`{bound} instantiates to {}",
        requirement_index + 1,
        crate::surface::diagnostics::describe_click_proposition(requirement),
        crate::surface::proof_diagnostics::render::render_proposition(lowered)
    )
}

fn is_integer_range_fold_theorem_name(name: &str) -> bool {
    matches!(
        name,
        "integer_range_fold_empty" | "integer_range_fold_append"
    )
}

/// Apply one of the kernel-issued symbolic Integer fold laws through the same
/// checked source theorem boundary as ordinary theorem applications.  These
/// laws are shape-directed: their sole argument must capture one Integer
/// `RangeFold`, and every guard emitted by the kernel law must be present in
/// the explicit `using` evidence set.
#[allow(clippy::too_many_arguments)]
fn instantiate_integer_range_fold_theorem_application(
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    tactic_index: usize,
    available: &[Proposition],
    assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, ClickError> {
    let error =
        |message: String| theorem_application_error(claim_label, path_index, tactic_index, message);
    if application.arguments.len() != 1 {
        return Err(error(format!(
            "theorem `{}` expects exactly one Integer fold argument, got {}",
            application.name,
            application.arguments.len()
        )));
    }
    let fold = capture_fixed_state_integer_expression(
        &application.arguments[0],
        context.integer_values,
        assumptions,
        context.values,
        context.array_refs,
        context.pre_state,
        context.post_state,
        context.result,
        context.recorded_snapshots,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        // The capture refusal already names which written subterm of the fold
        // carries the undischarged condition, or says that the argument did
        // not denote one value at all. Keep that failure distinct from the
        // later non-fold shape check and pass its wording through.
        error(format!(
            "could not capture Integer fold argument: {message}"
        ))
    })?;
    let crate::kernel::IntegerTerm::RangeFold {
        index,
        initial,
        accumulator,
        item,
        body,
    } = fold
    else {
        return Err(error(format!(
            "theorem `{}` requires one Integer range-fold argument",
            application.name
        )));
    };

    let theorem = match application.name.as_str() {
        "integer_range_fold_empty" => crate::kernel::prove_integer_range_fold_empty(
            index,
            initial.as_ref().clone(),
            accumulator,
            item,
            body.as_ref().clone(),
        ),
        "integer_range_fold_append" => crate::kernel::prove_integer_range_fold_append(
            index,
            initial.as_ref().clone(),
            accumulator,
            item,
            body.as_ref().clone(),
        )
        .ok_or_else(|| {
            error(
                "the Integer fold append law could not instantiate its checked next-element step"
                    .to_string(),
            )
        })?,
        _ => unreachable!("checked by is_integer_range_fold_theorem_name"),
    };
    let crate::kernel::Proposition::Implies(guard, conclusion) = theorem.proposition() else {
        return Err(error(
            "the Integer fold kernel law did not produce a guarded theorem".to_string(),
        ));
    };
    let mut required = Vec::new();
    collect_conjunctive_guard_facts(guard, &mut required);
    for premise in required {
        if !exact_fact_is_available(premise, available)
            && !matches!(normalize_proposition(premise), SimpProposition::True)
        {
            return Err(error(format!(
                "required exact fold guard is unavailable: {}",
                describe_pure_fact(premise, &[], &[])
            )));
        }
    }
    Ok(vec![conclusion.as_ref().clone()])
}

fn collect_conjunctive_guard_facts<'a>(
    proposition: &'a Proposition,
    facts: &mut Vec<&'a Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            collect_conjunctive_guard_facts(left, facts);
            collect_conjunctive_guard_facts(right, facts);
        }
        proposition => facts.push(proposition),
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_generic_theorem_application(
    definition: &TheoremDefinition,
    application: &TheoremApplication,
    theorem_environment: &TheoremEnvironment,
    assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<TheoremDefinition, String> {
    let concrete = instantiate_generic_theorem_application_definition(
        definition,
        application,
        assumptions,
        context,
        predicate_environment,
        click_function_environment,
    )?;
    if definition.type_parameters().is_empty() {
        return Ok(concrete);
    }
    if theorem_environment.generic_instance_is_verified(concrete.name()) {
        return Ok(concrete);
    }
    if !theorem_environment.begin_generic_instance_verification(concrete.name()) {
        return Err(format!(
            "cyclic verification of generic theorem instance `{}`",
            concrete.name()
        ));
    }
    let result = verify_concrete_theorem_definition(
        &concrete,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        None,
    )
    .map(|_| ())
    .map_err(|error| {
        format!(
            "generic theorem instance `{}` failed verification: {}",
            concrete.name(),
            error.message()
        )
    });
    theorem_environment.finish_generic_instance_verification(concrete.name(), result.is_ok());
    result?;
    Ok(concrete)
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn instantiate_generic_theorem_application_definition(
    definition: &TheoremDefinition,
    application: &TheoremApplication,
    assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<TheoremDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(definition.clone());
    }
    if application.arguments.len() != definition.parameters().len() {
        return Ok(definition.clone());
    }
    let argument_types = application
        .arguments
        .iter()
        .map(|argument| {
            theorem_application_argument_type(
                argument,
                assumptions,
                context,
                predicate_environment,
                click_function_environment,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let substitution = generics::infer_type_substitution(
        "theorem",
        definition.name(),
        definition.type_parameters(),
        definition
            .parameters()
            .iter()
            .map(|parameter| parameter.click_type().clone()),
        argument_types,
    )?;
    generics::instantiate_theorem(definition, &substitution)
}

#[allow(clippy::too_many_arguments)]
fn theorem_application_argument_type(
    argument: &ContractExpression,
    assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Option<ClickType>, String> {
    match argument {
        ContractExpression::AlgebraicVariable { algebraic_type, .. }
        | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
            return Ok(Some(ClickType::Algebraic(algebraic_type.clone())));
        }
        ContractExpression::CFragment(CExpression::Value(value)) => {
            return Ok(Some(ClickType::C(generics::c0_type_from_kernel(
                value.c_type(),
            ))));
        }
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => {
            if let Some(value) = context.values.get(name) {
                return Ok(Some(ClickType::C(generics::c0_type_from_kernel(
                    value.c_type(),
                ))));
            }
        }
        _ => {}
    }

    if let Ok(value) = capture_fixed_state_algebraic_expression(
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
    ) {
        return Ok(Some(generics::click_type_from_algebraic_value_type(
            &value.algebraic_type.value_type(),
        )));
    }

    let mut active_functions = BTreeSet::new();
    evaluate_contract_expression_with_environment(
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
    )
    .map(|value| Some(ClickType::C(generics::c0_type_from_kernel(value.c_type()))))
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
        crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    ),
    String,
> {
    let mut active_functions = BTreeSet::new();
    let mut values = BTreeMap::new();
    let mut array_refs = BTreeMap::new();
    let mut algebraic_values = BTreeMap::new();
    // Callee parameters are substituted simultaneously.  Keep the caller's
    // bindings as the immutable lookup environment, and accumulate the
    // resulting parameter bindings separately; otherwise an earlier callee
    // parameter can capture a later argument with the same spelling.
    let mut integer_values = crate::persistent::PersistentMap::default();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        if parameter.click_type() == &ClickType::Integer {
            let value = crate::surface::lowering::lower_contract_integer_to_spec(
                argument,
                context.integer_values,
            )?;
            integer_values = integer_values.with_inserted(parameter.name().to_string(), value);
            continue;
        }
        let Some(parameter_type) = parameter.click_type().c_type() else {
            let ClickType::Algebraic(expected_type) = parameter.click_type() else {
                return Err(format!(
                    "theorem `{}` parameter `{}` has unresolved type {}",
                    theorem.name(),
                    parameter.name(),
                    validation::describe_click_type(parameter.click_type())
                ));
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
            fn click_type_matches_algebraic_value_type(
                expected: &ClickType,
                actual: &crate::kernel::AlgebraicValueType,
            ) -> bool {
                match (expected, actual) {
                    (
                        ClickType::Algebraic(expected),
                        crate::kernel::AlgebraicValueType::Parameter(name),
                    ) => expected.rigid && expected.name == *name,
                    (ClickType::C(expected), crate::kernel::AlgebraicValueType::C(actual)) => {
                        expected.to_kernel_type() == *actual
                    }
                    (
                        ClickType::Algebraic(expected),
                        crate::kernel::AlgebraicValueType::Algebraic { name, arguments },
                    ) => {
                        !expected.rigid
                            && expected.name == *name
                            && expected.arguments.len() == arguments.len()
                            && expected
                                .arguments
                                .iter()
                                .zip(arguments)
                                .all(|(expected, actual)| {
                                    click_type_matches_algebraic_value_type(expected, actual)
                                })
                    }
                    _ => false,
                }
            }
            let type_matches = value.algebraic_type.rigid == expected_type.rigid
                && value.algebraic_type.name == expected_type.name
                && value.algebraic_type.arguments.len() == expected_type.arguments.len()
                && expected_type
                    .arguments
                    .iter()
                    .zip(&value.algebraic_type.arguments)
                    .all(|(expected, actual)| {
                        click_type_matches_algebraic_value_type(expected, actual)
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
        // The C null pointer constant at a pointer-typed theorem parameter is
        // that pointer type's null value, exactly as at a pure function's
        // pointer parameter, so a whole-tree claim can be stated at the null
        // parent (`parent_consistent(t, 0)`).
        if crate::surface::lowering::argument_is_null_pointer_constant(argument, parameter_type) {
            let pointer = CValue::typed_pointer(
                crate::kernel::Pointer::null(),
                parameter_type.to_kernel_type(),
            );
            if let Some(element_type) = click_array_element_type(parameter_type) {
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        memory: context.post_state.memory().clone(),
                        pointer: crate::kernel::Pointer::null(),
                        element_type,
                    },
                );
            }
            values.insert(parameter.name().to_string(), pointer);
            continue;
        }
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
    Ok((values, array_refs, algebraic_values, integer_values))
}

pub(super) fn theorem_application_pointer_element_widths(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
) -> BTreeMap<String, u32> {
    theorem
        .parameters()
        .iter()
        .zip(&application.arguments)
        .filter_map(|(parameter, argument)| {
            pointer_element_width_for_argument(argument, &context.pointer_element_widths)
                .map(|width| (parameter.name().to_string(), width))
        })
        .collect()
}

/// The memory each array parameter reads in, for the parameters whose
/// argument names a state of its own.
///
/// [`evaluate_fixed_state_array_ref_through_kernel`] gives an `old(...)` or
/// `at(...)` argument the memory of the state it names, and the theorem's own
/// indexing of that parameter has to read there: otherwise the premises are
/// checked, and the conclusion stated, at the application's current memory,
/// which is a different array than the one the argument named. An argument
/// read at the application's own state is left out, so an ordinary
/// application attaches no memory to its clauses and keeps lowering exactly
/// as before.
pub(in crate::surface::proof) fn theorem_application_bound_array_memories(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    array_refs: &ClickArrayRefs,
) -> BTreeMap<String, SpecMemory> {
    theorem
        .parameters()
        .iter()
        .zip(&application.arguments)
        .filter(|(_, argument)| {
            matches!(
                argument,
                ContractExpression::Old(_) | ContractExpression::At { .. }
            )
        })
        .filter_map(|(parameter, _)| {
            let array_ref = array_refs.get(parameter.name())?;
            Some((
                parameter.name().to_string(),
                SpecMemory::Fixed(array_ref.memory.clone()),
            ))
        })
        .collect()
}

/// Preserve a caller's physical pointer width through the expression that is
/// substituted for a theorem parameter.  Only pointer-preserving C forms are
/// followed; an opaque expression remains unsupported rather than receiving a
/// nominal carrier width.
fn pointer_element_width_for_argument(
    argument: &ContractExpression,
    known: &BTreeMap<String, u32>,
) -> Option<u32> {
    match argument {
        ContractExpression::Binding(name) | ContractExpression::CBinding(name) => {
            known.get(name).copied()
        }
        ContractExpression::CFragment(expression)
        | ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => pointer_element_width_for_c_expression(expression, known),
        ContractExpression::Add(left, right) => pointer_element_width_for_argument(left, known)
            .or_else(|| pointer_element_width_for_argument(right, known)),
        ContractExpression::Subtract(left, _)
        | ContractExpression::Index(left, _)
        | ContractExpression::Old(left)
        | ContractExpression::Negate(left)
        | ContractExpression::BitwiseNot(left) => pointer_element_width_for_argument(left, known),
        ContractExpression::At { expression, .. } => {
            pointer_element_width_for_argument(expression, known)
        }
        _ => None,
    }
}

fn pointer_element_width_for_c_expression(
    expression: &CExpression,
    known: &BTreeMap<String, u32>,
) -> Option<u32> {
    match expression {
        CExpression::Variable(name) => known.get(name).copied(),
        CExpression::Add(left, right) => pointer_element_width_for_c_expression(left, known)
            .or_else(|| pointer_element_width_for_c_expression(right, known)),
        CExpression::Subtract(left, _)
        | CExpression::PointerOffsetBytes { pointer: left, .. }
        | CExpression::Cast {
            expression: left, ..
        } => pointer_element_width_for_c_expression(left, known),
        _ => None,
    }
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
