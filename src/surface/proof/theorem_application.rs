use super::*;

thread_local! {
    static APPLICATION_SOURCE: std::cell::RefCell<Option<std::rc::Rc<TheoremApplication>>> = const { std::cell::RefCell::new(None) };
}

/// The checker resolves proof bindings to values. Retain just this tactic's
/// written arguments for diagnostics; never consult them to decide a proof.
pub(super) fn with_application_source<T>(
    application: &TheoremApplication,
    check: impl FnOnce() -> T,
) -> T {
    struct Restore(Option<std::rc::Rc<TheoremApplication>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            APPLICATION_SOURCE.with(|source| *source.borrow_mut() = self.0.take());
        }
    }
    let prior = APPLICATION_SOURCE
        .with(|source| source.replace(Some(std::rc::Rc::new(application.clone()))));
    let _restore = Restore(prior);
    check()
}

fn requirement_source_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
) -> Vec<(String, ContractExpression)> {
    let written = APPLICATION_SOURCE.with(|source| source.borrow().clone());
    let source = written
        .as_deref()
        .filter(|written| {
            written.name == application.name
                && written.arguments.len() == application.arguments.len()
        })
        .unwrap_or(application);
    theorem
        .parameters()
        .iter()
        .zip(&source.arguments)
        .map(|(parameter, argument)| (parameter.name().to_owned(), argument.clone()))
        .collect()
}

pub(super) struct TheoremApplicationContext<'a> {
    pub(super) values: &'a BTreeMap<String, CValue>,
    pub(super) array_refs: &'a ClickArrayRefs,
    pub(super) algebraic_values: &'a BTreeMap<String, SpecAlgebraicExpression>,
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

/// Adds a cited range premise's extent guards to an explicit evidence list.
///
/// Citing a stated range cites what the range says: `loadable(p[a..b])`
/// means `a..b` is a valid 32-bit byte extent and those bytes are loadable,
/// and theorem instantiation asks the application for both halves. A `using`
/// list that names the range has therefore named both, and the endpoint
/// spelling of the `fits` half is an unsigned comparison the surface cannot
/// write at all. This relaxes the restriction only: a guard joins the list
/// solely where `available` already holds it, so nothing is derived and no
/// ambient fact becomes evidence for anything else.
///
/// Every checker that turns a `using` list into evidence (`apply using` in
/// pure and fixed-state proofs, `transport using`) calls this one rule, and
/// smart theorem selection proposes a range premise only when
/// [`missing_theorem_extent_guard`] finds nothing this rule would leave out.
pub(super) fn cite_range_extent_guards(
    premise: &Proposition,
    evidence: &mut Vec<Proposition>,
    available: impl Fn(&Proposition) -> bool,
) {
    for guard in crate::kernel::stated_loadable_extent_guard_spellings(premise) {
        if !evidence.contains(&guard) && available(&guard) {
            evidence.push(guard);
        }
    }
}

/// The first extent guard a theorem requirement owes that an application
/// citing the requirement cannot supply.
///
/// This is the search-side mirror of the check in
/// `instantiate_theorem_application_with_assumptions`: that check asks for
/// each count-form guard among the evidence, and [`cite_range_extent_guards`]
/// puts it there exactly when it is available. A selector that lists the
/// range requirement therefore owes nothing more when this returns `None`,
/// and would be refused by the checker when it returns a guard.
pub(super) fn missing_theorem_extent_guard(
    requirement: &Proposition,
    available: impl Fn(&Proposition) -> bool,
) -> Option<Proposition> {
    crate::kernel::stated_loadable_extent_guards(requirement)
        .into_iter()
        .find(|guard| {
            !available(guard) && !matches!(normalize_proposition(guard), SimpProposition::True)
        })
}

pub(super) fn apply_theorem_applications_to_available(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    available: Vec<Proposition>,
    context: &TheoremApplicationContext<'_>,
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
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
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    for (tactic_index, application) in theorem_applications {
        available =
            unfold_available_predicate_facts(spec_definitions, unfolded_predicates, &available)
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
            spec_definitions,
            unfolded_predicates,
        )?;
        for conclusion in conclusions {
            if !available.contains(&conclusion) {
                available.push(conclusion);
            }
        }
    }
    unfold_available_predicate_facts(spec_definitions, unfolded_predicates, &available)
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
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
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
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    if application.name == "declared_uint32_from_bytes" {
        return super::uint32_representation::instantiate_declared_uint32_from_bytes(
            application,
            claim_label,
            path_index,
            tactic_index,
            available,
            assumptions,
            context,
            spec_definitions,
        );
    }
    if is_integer_range_fold_theorem_name(&application.name) {
        return instantiate_integer_range_fold_theorem_application(
            application,
            claim_label,
            path_index,
            tactic_index,
            available,
            assumptions,
            context,
            spec_definitions,
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
        spec_definitions,
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
        spec_definitions,
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
            spec_definitions,
            &BTreeSet::new(),
            pointer_element_widths.clone(),
        )
    };

    let requirements =
        crate::surface::proof::pure_theorems::theorem_requirement_propositions(&theorem).map_err(
            |error| theorem_application_error(claim_label, path_index, tactic_index, error.message),
        )?;
    for (requirement_index, requirement) in requirements.iter().enumerate() {
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
            spec_definitions,
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
        // A requirement is also met by a listed fact that states the same
        // order claim from the other side, `c >= b` for `b <= c`, in any
        // order family: the kernel's `int32` order lemmas accept that
        // spelling, and the standard library's 64-bit ones are applied here.
        let mirrored_order_listed = || {
            crate::kernel::proof::fact_reasoning::order_claim_forms(&lowered)
                .iter()
                .any(|form| exact_fact_is_available(form, available))
        };
        if !crate::kernel::listed_premise_holds(&lowered, |premise| {
            exact_fact_is_available(premise, available)
        }) && !mirrored_order_listed()
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
                    &requirement_source_bindings(&theorem, application),
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
                {
                    // The guard is spelled through the caller's own value
                    // names, so the reader sees the fact they have to supply
                    // (`n <= 1073741823`) rather than `int32 <=(v1, …)`.
                    let (parameters, arguments) =
                        crate::surface::diagnostics::value_naming_tables(context.values);
                    format!(
                        "theorem `{}` requirement {} `{}` states a memory range, so applying it \
                         needs that range to be a valid 32-bit byte extent here: `{}` is not an \
                         available fact. A range's extent is `(end - start) * width` in 32-bit \
                         arithmetic, and without that bound it can wrap to fewer bytes than its \
                         element count names",
                        theorem.name(),
                        requirement_index + 1,
                        crate::surface::diagnostics::describe_click_proposition(requirement),
                        crate::surface::diagnostics::describe_pure_fact_spelled(
                            &guard,
                            &parameters,
                            &arguments,
                        ),
                    )
                },
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
    bindings: &[(String, ContractExpression)],
    lowered: &Proposition,
) -> String {
    // Substitute the actual written arguments rather than asking a kernel
    // load to recover the state selector the author already supplied.
    let substitutions = bindings.iter().cloned().collect::<BTreeMap<_, _>>();
    let instantiation = substitute_click_proposition(requirement, &substitutions)
        .map(|surface| crate::surface::printing::source_click_proposition(&surface))
        .unwrap_or_else(|_| crate::surface::proof_diagnostics::render::render_proposition(lowered));
    let names = bindings
        .iter()
        .map(|(name, value)| {
            (
                name.clone(),
                crate::surface::diagnostics::describe_contract_expression(value),
            )
        })
        .collect::<Vec<_>>();
    describe_unavailable_theorem_requirement_spelled(
        theorem_name,
        requirement_index,
        requirement,
        &names,
        &instantiation,
    )
}

/// [`describe_unavailable_theorem_requirement`] with the instantiation
/// already spelled, for a caller that holds the names the proof state gives
/// the lowered terms.
pub(super) fn describe_unavailable_theorem_requirement_spelled(
    theorem_name: &str,
    requirement_index: usize,
    requirement: &ClickProposition,
    bindings: &[(String, String)],
    instantiation: &str,
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
        instantiation
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
    spec_definitions: SpecDefinitions<'_>,
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
        spec_definitions,
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

pub(super) fn collect_conjunctive_guard_facts<'a>(
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
    spec_definitions: SpecDefinitions<'_>,
) -> Result<TheoremDefinition, String> {
    let concrete = instantiate_generic_theorem_application_definition(
        definition,
        application,
        assumptions,
        context,
        spec_definitions,
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
    let result =
        verify_concrete_theorem_definition(&concrete, spec_definitions, theorem_environment, None)
            .map(|_| ())
            .map_err(|error| {
                format!(
                    "generic theorem instance `{}` failed verification: {}",
                    concrete.name(),
                    error.raw_summary()
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
    spec_definitions: SpecDefinitions<'_>,
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
            theorem_application_argument_type(argument, assumptions, context, spec_definitions)
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
    spec_definitions: SpecDefinitions<'_>,
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
        context.values,
        context.array_refs,
        context.pre_state,
        context.post_state,
        context.result,
        context.recorded_snapshots,
        spec_definitions,
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
        spec_definitions,
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
    spec_definitions: SpecDefinitions<'_>,
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
            let value = match crate::surface::lowering::lower_contract_integer_to_spec(
                argument,
                context.integer_values,
            ) {
                Ok(value) => value,
                Err(_) => crate::kernel::SpecIntegerExpression::Term(
                    capture_fixed_state_integer_expression(
                        argument,
                        context.integer_values,
                        assumptions,
                        context.values,
                        context.array_refs,
                        context.pre_state,
                        context.post_state,
                        context.result,
                        context.recorded_snapshots,
                        spec_definitions,
                    )?,
                ),
            };
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
            let algebraic_bindings = contract_expression_referenced_names(argument)
                .into_iter()
                .filter_map(|name| {
                    context
                        .algebraic_values
                        .get(&name)
                        .cloned()
                        .map(|value| (name, value))
                })
                .collect();
            let value = capture_fixed_state_algebraic_expression_with_values(
                argument,
                context.values,
                context.array_refs,
                algebraic_bindings,
                context.pre_state,
                context.post_state,
                context.result,
                context.recorded_snapshots,
                spec_definitions,
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
                spec_definitions,
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
                spec_definitions,
                context.recorded_snapshots,
                &mut active_functions,
            )?;
            if !c_value_matches_click_type(&value, parameter_type) {
                let (naming_parameters, naming_arguments) =
                    crate::surface::diagnostics::value_naming_tables(context.values);
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {}, got `{}` of type `{}`",
                    theorem.name(),
                    parameter.name(),
                    describe_c0_type(parameter_type),
                    crate::surface::diagnostics::describe_c_value(
                        &value,
                        &naming_parameters,
                        &naming_arguments
                    ),
                    crate::kernel::c_type_spelling(value.c_type())
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
        CExpression::MemberAddress { selection, .. } => Some(selection.value_type.byte_width()),
        CExpression::RecordPointerOffset { layout, .. } => Some(layout.size_bytes()),
        CExpression::Add(left, right) => pointer_element_width_for_c_expression(left, known)
            .or_else(|| pointer_element_width_for_c_expression(right, known)),
        CExpression::Subtract(left, _)
        | CExpression::PointerOffsetBytes { pointer: left, .. }
        | CExpression::PointerAligned { pointer: left, .. }
        | CExpression::Cast {
            expression: left, ..
        } => pointer_element_width_for_c_expression(left, known),
        _ => None,
    }
}

pub(super) fn theorem_application_error(
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

#[cfg(test)]
mod observed_integer_argument_tests {
    use super::*;

    #[test]
    fn integer_equality_citations_preserve_orientation_polarity_and_certificates() {
        let source = r#"
            theorem equal_arguments(a: Integer, b: Integer) {
                requires a == b;
                ensures a == b by { assumption(); }
            }
            theorem reverse_requirement(a: Integer, b: Integer) {
                requires b == a;
                ensures a == b by {
                    apply(equal_arguments(a, b)) using { b == a; }
                }
            }
            theorem reverse_citation(a: Integer, b: Integer) {
                requires b == a;
                ensures a == b by {
                    apply(equal_arguments(a, b)) using { a == b; }
                }
            }
            theorem reverse_transport(a: Integer, b: Integer) {
                requires b == a;
                ensures a == b by {
                    transport(b == a, a == b) using { b == a; }
                }
            }
            theorem reverse_observations(a: uint32, b: uint32) {
                requires to_integer(b) == to_integer(a);
                ensures to_integer(a) == to_integer(b) by {
                    apply(equal_arguments(to_integer(a), to_integer(b))) using {
                        to_integer(b) == to_integer(a);
                    }
                }
            }
        "#;
        verify_c0_sources(source, &[]).unwrap();
        for label in [
            "reverse_requirement",
            "reverse_citation",
            "reverse_transport",
            "reverse_observations",
        ] {
            let expanded =
                expand_c0_claim_source_by_label(source, &[], &format!("{label}.ensures_0"))
                    .unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
        }
        for (before, after) in [
            ("requires b == a;", ""),
            ("requires b == a;", "requires b != a;"),
            ("equal_arguments(a, b)", "equal_arguments(a + 1, b)"),
            ("using { b == a; }", "using {}"),
            ("transport(b == a, a == b)", "transport(b == a, a != b)"),
            (
                "requires to_integer(b) == to_integer(a);",
                "requires to_integer(b) != to_integer(a);",
            ),
        ] {
            let invalid = source.replace(before, after);
            assert_ne!(source, invalid);
            assert!(
                verify_c0_sources(&invalid, &[]).is_err(),
                "accepted {before} -> {after}"
            );
        }
    }

    #[test]
    fn integer_theorem_observed_arguments_preserve_types_guards_and_expansion() {
        let prefix = "theorem reflexive(z: Integer) { ensures z == z by simp; } ";
        for (ty, expression, guard) in [
            ("int32", "x + 1", "defined(x + 1)"),
            ("int64", "x + 1i64", "defined(x + 1i64)"),
            ("int128", "x / (int128)3", "defined(x / (int128)3)"),
        ] {
            let source = format!(
                "{prefix} theorem observed(x: {ty}) {{ requires {guard}; ensures to_integer({expression}) == to_integer({expression}) by {{ apply(reflexive(to_integer({expression}))); }} }}"
            );
            verify_c0_sources(&source, &[])
                .unwrap_or_else(|error| panic!("{ty}: {}", error.message()));
            let expanded =
                expand_c0_claim_source_by_label(&source, &[], "observed.ensures_0").unwrap();
            verify_c0_sources(&expanded, &[]).unwrap();
            if ty != "int128" {
                let apply_start = expanded.find("apply(reflexive(").unwrap();
                let using_start = apply_start + expanded[apply_start..].find("using {").unwrap();
                let using_end = using_start + expanded[using_start..].find('}').unwrap() + 1;
                let erased = format!(
                    "{}using {{}}{}",
                    &expanded[..using_start],
                    &expanded[using_end..]
                );
                assert!(
                    verify_c0_sources(&erased, &[]).is_err(),
                    "erased argument guard was accepted"
                );
                let missing = source.replace(&format!("requires {guard};"), "");
                assert!(verify_c0_sources(&missing, &[]).is_err());
            }
        }
        for argument in [
            "to_integer(true)",
            "true",
            "to_integer(2147483647 + 1)",
            "truncating_quotient(to_integer(x), 0)",
            "to_integer(x / 0)",
        ] {
            let source = format!(
                "{prefix} theorem refused(x: int32) {{ ensures x == x by {{ apply(reflexive({argument})); simp(); }} }}"
            );
            let Err(error) = verify_c0_sources(&source, &[]) else {
                panic!("invalid argument accepted: {argument}");
            };
            assert!(error.message().len() < 8000);
        }
    }

    #[test]
    fn integer_theorem_arguments_capture_current_entry_snapshot_and_result_values() {
        let parsed = crate::surface::parser::parse_file_items(
            "theorem reflexive(z: Integer) { ensures z == z by simp; }",
        )
        .unwrap();
        let theorem = &parsed.theorem_definitions()[0];
        let pre_state = CState::new().with_local("x", int32(7u32));
        let post_state = pre_state.clone().with_local("x", int32(9u32));
        let values = BTreeMap::new();
        let arrays = BTreeMap::new();
        let algebraic = BTreeMap::new();
        let integers = crate::persistent::PersistentMap::default();
        let result = int32(11u32);
        let mut snapshots = RecordedSnapshots::default();
        snapshots.insert(SnapshotSelector::Mark("before".into()), pre_state.clone());
        let context = TheoremApplicationContext {
            values: &values,
            array_refs: &arrays,
            algebraic_values: &algebraic,
            pre_state: &pre_state,
            post_state: &post_state,
            result: Some(&result),
            recorded_snapshots: &snapshots,
            integer_values: &integers,
            pointer_element_widths: BTreeMap::new(),
        };
        let x = ContractExpression::Binding("x".into());
        for (argument, expected) in [
            (x.clone(), 9),
            (ContractExpression::Old(Box::new(x.clone())), 7),
            (
                ContractExpression::At {
                    selector: SnapshotSelector::Mark("before".into()),
                    expression: Box::new(x),
                },
                7,
            ),
            (
                ContractExpression::Binding(crate::kernel::C_CONTRACT_RESULT_NAME.into()),
                11,
            ),
        ] {
            let application = TheoremApplication {
                name: "reflexive".into(),
                arguments: vec![ContractExpression::Call {
                    name: "to_integer".into(),
                    arguments: vec![argument],
                }],
            };
            let (_, _, _, bound) = theorem_application_bindings(
                theorem,
                &application,
                &context,
                &PureFactContext::new(),
                SpecDefinitions::new(
                    &PredicateEnvironment::new(&[]),
                    &ClickFunctionEnvironment::new(&[]),
                ),
            )
            .unwrap();
            assert_eq!(
                bound.get("z"),
                Some(&crate::kernel::SpecIntegerExpression::Term(
                    crate::kernel::IntegerTerm::constant_i64(expected)
                ))
            );
        }
    }

    #[test]
    fn integer_theorem_argument_capture_scales_with_unused_bindings_and_applications() {
        let mut work_samples = Vec::new();
        for size in [4usize, 16, 64, 256] {
            let source = "theorem reflexive(z: Integer) { ensures z == z by simp; }";
            let parsed = crate::surface::parser::parse_file_items(source).unwrap();
            let theorem = &parsed.theorem_definitions()[0];
            let application = TheoremApplication {
                name: "reflexive".into(),
                arguments: vec![ContractExpression::Call {
                    name: "to_integer".into(),
                    arguments: vec![ContractExpression::Binding("x".into())],
                }],
            };
            let mut state = CState::new().with_local("x", int32(7u32));
            let mut values = BTreeMap::new();
            values.insert("x".into(), int32(7));
            for i in 0..size {
                let name = format!("unused_{i}");
                state = state.with_local(name.clone(), int32(i as u32));
                values.insert(name, int32(i as u32));
            }
            let array_refs = BTreeMap::new();
            let algebraic_values = BTreeMap::new();
            let integer_values = crate::persistent::PersistentMap::default();
            let snapshots = RecordedSnapshots::default();
            let context = TheoremApplicationContext {
                values: &values,
                array_refs: &array_refs,
                algebraic_values: &algebraic_values,
                pre_state: &state,
                post_state: &state,
                result: None,
                recorded_snapshots: &snapshots,
                integer_values: &integer_values,
                pointer_element_widths: BTreeMap::new(),
            };
            let assumptions = PureFactContext::new();
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let spec_definitions = SpecDefinitions::new(&predicates, &functions);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                theorem_application_bindings(
                    theorem,
                    &application,
                    &context,
                    &assumptions,
                    spec_definitions,
                )
            });
            let (_, _, _, bound) = result.unwrap();
            assert_eq!(
                bound.get("z"),
                Some(&crate::kernel::SpecIntegerExpression::Term(
                    crate::kernel::IntegerTerm::constant_i64(7)
                ))
            );
            work_samples.push(work);
            let (result, repeated_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    for _ in 0..size {
                        theorem_application_bindings(
                            theorem,
                            &application,
                            &context,
                            &assumptions,
                            spec_definitions,
                        )?;
                    }
                    Ok::<_, String>(())
                });
            result.unwrap();
            assert_eq!(repeated_work, size * work);
        }
        assert!(
            work_samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{work_samples:?}"
        );
    }
}

#[cfg(test)]
mod diagnostic_source_tests {
    use super::*;

    #[test]
    fn application_diagnostic_source_restores_after_nested_failures() {
        let outer = TheoremApplication {
            name: "outer".into(),
            arguments: vec![ContractExpression::Binding("r".into())],
        };
        let inner = TheoremApplication {
            name: "inner".into(),
            arguments: vec![],
        };
        assert!(APPLICATION_SOURCE.with(|source| source.borrow().is_none()));
        with_application_source(&outer, || {
            let error = with_application_source(&inner, || {
                assert_eq!(
                    APPLICATION_SOURCE.with(|source| source
                        .borrow()
                        .as_ref()
                        .unwrap()
                        .name
                        .clone()),
                    "inner"
                );
                Err::<(), _>("refused")
            });
            assert_eq!(error, Err("refused"));
            assert_eq!(
                APPLICATION_SOURCE.with(|source| source.borrow().as_ref().unwrap().name.clone()),
                "outer"
            );
        });
        assert!(APPLICATION_SOURCE.with(|source| source.borrow().is_none()));
    }
}
