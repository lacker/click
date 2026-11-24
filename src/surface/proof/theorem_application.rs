use super::*;
use crate::kernel::proof::fact_reasoning::listed_comparison_fact_is_available;

thread_local! {
    static APPLICATION_SOURCE: std::cell::RefCell<Option<std::rc::Rc<TheoremApplication>>> = const { std::cell::RefCell::new(None) };
}

thread_local! {
    static PREPARING_APPLICATION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(in crate::surface::proof) fn preparing_application() -> bool {
    PREPARING_APPLICATION.with(std::cell::Cell::get)
}

pub(in crate::surface::proof) fn with_application_preparation<T>(prepare: impl FnOnce() -> T) -> T {
    with_application_preparation_mode(true, prepare)
}

fn with_application_preparation_mode<T>(active: bool, operation: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            PREPARING_APPLICATION.with(|active| active.set(self.0));
        }
    }
    let _restore = Restore(PREPARING_APPLICATION.with(|current| current.replace(active)));
    operation()
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
    pub(super) parameters: ParameterBinding<'a>,
    pub(super) values: &'a ProgramValueBindings,
    pub(super) array_refs: &'a ClickArrayRefs,
    pub(super) algebraic_values: &'a BTreeMap<String, SpecAlgebraicExpression>,
    pub(super) pre_state: &'a ExecutionState,
    pub(super) post_state: &'a ExecutionState,
    pub(super) result: Option<&'a ProgramValue>,
    pub(super) recorded_states: &'a RecordedStates,
    pub(super) integer_values: &'a PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    /// Physical pointee widths for C parameters in the caller's scope.  A
    /// theorem application may rename such a parameter, so the application
    /// binding maps this by argument expression before lowering the callee's
    /// propositions.
    pub(super) pointer_element_widths: BTreeMap<String, u32>,
}

/// Adds a cited range premise's span guards to an explicit evidence list.
///
/// Citing a stated range cites what the range says: `loadable(p[a..b])`
/// means `a..b` is a valid 32-bit byte span and those bytes are loadable,
/// and theorem instantiation asks the application for both halves. A `using`
/// list that names the range has therefore named both, and the endpoint
/// spelling of the `fits` half is an unsigned comparison the surface cannot
/// write at all. This relaxes the restriction only: a guard joins the list
/// solely where `available` already holds it, so nothing is derived and no
/// ambient fact becomes evidence for anything else.
///
/// Every checker that turns a `using` list into evidence (`apply using` in
/// pure and fixed-state proofs, `transport using`) calls this one rule.
pub(super) fn cite_range_span_guards(
    premise: &Proposition,
    evidence: &mut Vec<Proposition>,
    available: impl Fn(&Proposition) -> bool,
) {
    for guard in crate::kernel::stated_loadable_span_guard_spellings(premise) {
        if !evidence.contains(&guard) && available(&guard) {
            evidence.push(guard);
        }
    }
}

/// Instantiates one theorem from explicit evidence and an indexed lowering
/// context. Index the evidence only when unfolding a requirement or applying
/// an Integer fold law needs it; ordinary exact requirements read the list.
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
    lowering_assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<Proposition>, ClickError> {
    let evidence_context = std::cell::OnceCell::new();
    let evidence_assumptions =
        || evidence_context.get_or_init(|| assumptions_from_propositions(available));
    if is_integer_range_fold_theorem_name(&application.name) {
        return instantiate_integer_range_fold_theorem_application(
            application,
            claim_label,
            path_index,
            tactic_index,
            available,
            if preparing_application() {
                lowering_assumptions
            } else {
                evidence_assumptions()
            },
            context,
            spec_definitions,
        );
    }
    if application.name == "population_member_count_zero" {
        return instantiate_population_member_count_zero(
            application,
            claim_label,
            path_index,
            tactic_index,
            available,
            lowering_assumptions,
            context,
            spec_definitions,
        );
    }
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        theorem_application_error(
            claim_label,
            path_index,
            tactic_index,
            format!(
                "unknown theorem `{}`{}",
                application.name,
                crate::surface::validation::library_import_hint(&application.name)
            ),
        )
    })?;
    let theorem = instantiate_generic_theorem_application_definition(
        theorem,
        application,
        lowering_assumptions,
        context,
        spec_definitions,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, tactic_index, message))?;
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
    let bind = |state: &ExecutionState| {
        values.iter().fold(state.clone(), |state, (name, value)| {
            state.with_local(name.clone(), value.clone())
        })
    };
    let pre_state = bind(context.pre_state);
    let post_state = bind(context.post_state);
    let pointer_element_widths = theorem_application_pointer_element_widths(
        &theorem,
        application,
        context,
        spec_definitions,
    );
    let bound_array_memories =
        theorem_application_bound_array_memories(&theorem, application, &array_refs);
    let resource_bindings = theorem_resource_argument_bindings(
        &theorem,
        application,
        context,
        lowering_assumptions,
        spec_definitions,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, tactic_index, message))?;
    let lower = |proposition: &ClickProposition| {
        let proposition = substitute_click_proposition(proposition, &resource_bindings)?;
        lower_fixed_state_proposition_through_kernel_with(
            &proposition,
            lowering_assumptions,
            ContractEnvironment::new(&values, &array_refs),
            FixedStateFrame::new(&pre_state, &post_state, None, context.recorded_states),
            spec_definitions,
            FixedStateLoweringOptions {
                algebraic_values: Some(&algebraic_values),
                integer_values: Some(&integer_values),
                bound_array_memories: Some(&bound_array_memories),
                pointer_element_widths: pointer_element_widths.clone(),
                ..Default::default()
            },
        )
    };

    let requirements =
        crate::surface::proof::pure_theorems::theorem_requirement_propositions(&theorem).map_err(
            |error| theorem_application_error(claim_label, path_index, tactic_index, error.message),
        )?;
    let prepared_bindings = preparing_application().then(|| {
        Arc::<[(String, ContractExpression)]>::from(requirement_source_bindings(
            &theorem,
            application,
        ))
    });
    let prepared_substitutions = prepared_bindings.as_ref().map(|bindings| {
        bindings
            .iter()
            .cloned()
            .zip(theorem.parameters())
            .map(|((name, value), parameter)| {
                let value = if parameter.click_type() == &ClickType::Integer {
                    crate::surface::proof::surface_synthesis::integer_typed_expression(value)
                } else {
                    value
                };
                (name, value)
            })
            .collect()
    });
    for (requirement_index, requirement) in requirements.iter().enumerate() {
        let lowered = lower(requirement).map_err(|error| {
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
        if let (Some(bindings), Some(substitutions)) = (&prepared_bindings, &prepared_substitutions)
        {
            let written =
                observe_machine_parameters(requirement, theorem.parameters(), substitutions);
            let surface =
                substitute_click_proposition(&written, substitutions).map_err(ClickError::new)?;
            crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                ClickError::new("theorem application has a premise obligation")
                    .with_spelled_requirement(
                        lowered.clone(),
                        surface,
                        format!("theorem `{}` premise", theorem.name()),
                    )
                    .with_theorem_requirement_source(TheoremRequirementSource {
                        index: requirement_index,
                        clause: requirement.clone(),
                        bindings: bindings.clone(),
                    }),
            )?;
            for guard in crate::kernel::stated_loadable_span_guards(&lowered) {
                crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                    ClickError::new("theorem range requires a valid span")
                        .with_unresolved_requirement(&ProofObligation::verification_condition(
                            guard,
                        )),
                )?;
            }
            continue;
        }
        // A named `using` premise may be a checked conjunction, such as the
        // `defined(x + y)` fact emitted for a C addition.  The theorem may
        // require one of that fact's proper conjuncts (the no-overflow
        // condition), so select it through the same exact structural rule as
        // an explicit implication application.  This does not derive or normalize a
        // weaker proposition: the complete conjunction remains the supplied
        // evidence and only its checked conjunct satisfies this requirement.
        // A requirement is also met by a listed fact that states the same
        // order claim from the other side, `c >= b` for `b <= c`, in any
        // order family: the kernel's `int32` order lemmas accept that
        // spelling, and the standard library's 64-bit ones are applied here.
        let mirrored_order_listed = || {
            crate::kernel::proof::fact_reasoning::order_claim_forms(&lowered)
                .iter()
                .any(|form| listed_comparison_fact_is_available(form, available))
        };
        if !crate::kernel::listed_premise_holds(&lowered, |premise| {
            listed_comparison_fact_is_available(premise, available)
        }) && !mirrored_order_listed()
            && !matches!(normalize_proposition(&lowered), NormalizedProposition::True)
        {
            let (message, fact) = describe_unavailable_theorem_requirement(
                theorem.name(),
                requirement_index,
                requirement,
                theorem.parameters(),
                &requirement_source_bindings(&theorem, application),
                &lowered,
            );
            return Err(
                theorem_application_error(claim_label, path_index, tactic_index, message)
                    .with_missing_theorem_requirement(format!(
                        "theorem `{}` needs listed prerequisite `{fact}`",
                        theorem.name()
                    )),
            );
        }
        // A range premise states two things, and the theorem's own proof
        // assumed both: that `a..b` is a valid 32-bit byte span, and that
        // those bytes are loadable. Applying it owes both, or a range that is
        // vacuously loadable because its span wrapped would hand the theorem
        // the valid-span fact it never established. The guards are spelled
        // over the element count, which is the spelling a proof can write.
        for guard in crate::kernel::stated_loadable_span_guards(&lowered) {
            if listed_comparison_fact_is_available(&guard, available)
                || matches!(normalize_proposition(&guard), NormalizedProposition::True)
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
                         needs that range to be a valid 32-bit byte span here: `{}` is not an \
                         available fact. A range's span is `(end - start) * width` in 32-bit \
                         arithmetic, and without that bound it can wrap to fewer bytes than its \
                         element count names",
                        theorem.name(),
                        requirement_index + 1,
                        crate::surface::diagnostics::describe_click_proposition(requirement),
                        crate::surface::diagnostics::describe_pure_fact_spelled(
                            &guard,
                            ParameterBinding::new(&parameters, &arguments),
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
        // The verified theorem already proves its conclusion's definedness
        // from the requirements checked above. Instantiating that conclusion
        // reconstructs its term; it must not demand a second proof during
        // lowering. Argument evaluation retains its own use-site checks.
        let conclusion =
            substitute_click_proposition(conclusion, &resource_bindings).map_err(|message| {
                theorem_application_error(claim_label, path_index, tactic_index, message)
            })?;
        let conclusion = lower_fixed_state_proposition_retaining_requirements(
            &conclusion,
            lowering_assumptions,
            ContractEnvironment::new(&values, &array_refs),
            FixedStateFrame::new(&pre_state, &post_state, None, context.recorded_states),
            spec_definitions,
            FixedStateLoweringOptions {
                algebraic_values: Some(&algebraic_values),
                integer_values: Some(&integer_values),
                bound_array_memories: Some(&bound_array_memories),
                pointer_element_widths: pointer_element_widths.clone(),
                ..Default::default()
            },
        )
        .map(|(proposition, _, _, _)| proposition)
        .map_err(|error| {
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
    parameters: &[FunctionParameter],
    bindings: &[(String, ContractExpression)],
    lowered: &Proposition,
) -> (String, String) {
    // Substitute the actual written arguments rather than asking a kernel
    // load to recover the program point selector the author already supplied. A
    // native comparison keeps its observations, so the instantiation reads
    // back as the requirement: `100u64 < a` at `a = n - k` is not the
    // Integer comparison `100u64 < n - k`.
    let substitutions = bindings.iter().cloned().collect::<BTreeMap<_, _>>();
    let observed = observe_machine_parameters(requirement, parameters, &substitutions);
    let instantiation = substitute_click_proposition(&observed, &substitutions)
        .map(|surface| crate::surface::printing::source_click_proposition(&surface))
        .unwrap_or_else(|_| crate::surface::proof_diagnostics::render::render_proposition(lowered));
    let detail = describe_theorem_requirement_instantiation(
        requirement_index,
        requirement,
        bindings,
        &instantiation,
    );
    let message =
        format!("required exact fact for theorem `{theorem_name}` is unavailable: {detail}");
    (message, instantiation)
}

/// Describe a premise whose instantiated goal is already spelled in the caller's names.
pub(super) fn describe_theorem_requirement_instantiation(
    requirement_index: usize,
    requirement: &ClickProposition,
    bindings: &[(String, ContractExpression)],
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
        .map(|(parameter, argument)| {
            let argument = crate::surface::diagnostics::describe_contract_expression(argument);
            format!("{parameter} = {argument}")
        })
        .collect::<Vec<_>>();
    let bound = if bound.is_empty() {
        String::new()
    } else {
        format!(" with {}", bound.join(", "))
    };
    format!(
        "requirement {} `{}`{bound} instantiates to {}",
        requirement_index + 1,
        crate::surface::diagnostics::describe_click_proposition(requirement),
        instantiation
    )
}

pub(super) fn is_integer_range_fold_theorem_name(name: &str) -> bool {
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
    // The fold law substitutes the captured body at a new index. Check the
    // body's scoped evaluation conditions before using that captured term.
    let fold = with_application_preparation_mode(false, || {
        capture_fixed_state_integer_expression(
            &application.arguments[0],
            context.integer_values,
            assumptions,
            ContractEnvironment::new(context.values, context.array_refs)
                .with_parameters(context.parameters),
            FixedStateFrame::new(
                context.pre_state,
                context.post_state,
                context.result,
                context.recorded_states,
            ),
            spec_definitions,
        )
    })
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
        if preparing_application() {
            crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                ClickError::new("Integer fold theorem has a premise obligation")
                    .with_unresolved_requirement(&ProofObligation::verification_condition(
                        premise.clone(),
                    )),
            )?;
            continue;
        }
        if !exact_fact_is_available(premise, available)
            && !matches!(normalize_proposition(premise), NormalizedProposition::True)
        {
            return Err(error(format!(
                "required exact fold guard is unavailable: {}",
                describe_pure_fact(premise, ParameterBinding::default())
            )));
        }
    }
    Ok(vec![conclusion.as_ref().clone()])
}

/// The checked step a bare `apply(population_member_count_zero(count(R(a, k))))`
/// stands for: its one premise is the written population count,
/// `count(R(a, _)) == 0`. `None` for any other application.
pub(in crate::surface::proof) fn population_member_count_zero_step(
    application: &TheoremApplication,
) -> Option<ProofStep> {
    if application.name != "population_member_count_zero" {
        return None;
    }
    let premises = match application.arguments.as_slice() {
        [ContractExpression::ResourceCount(resource)] => {
            let mut population = resource.as_ref().clone();
            if let ResourceClause::Declared { arguments, .. } = &mut population {
                for argument in arguments.iter_mut().skip(1) {
                    *argument = ContractExpression::ResourceWildcard;
                }
            }
            vec![ClickProposition::Comparison {
                left: ContractExpression::ResourceCount(Box::new(population)),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::IntegerLiteral("0".to_string()),
            }]
        }
        // The checked application names the expected shape.
        _ => Vec::new(),
    };
    Some(ProofStep::ApplyPlannedTheorem {
        application: application.clone(),
        premises,
    })
}

/// Apply the kernel's empty-population law to one written exact-member count,
/// `population_member_count_zero(count(R(anchor, k, ...)))`. The kernel
/// evaluates the member's and the population's counts itself; the written
/// population count `count(R(anchor, _, ...)) == 0` must be an available fact,
/// and the member's count `== 0` is added.
#[allow(clippy::too_many_arguments)]
fn instantiate_population_member_count_zero(
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
    let shape = || {
        error(format!(
            "theorem `{}` expects one exact member count, `count(R(anchor, k, ...))`",
            application.name
        ))
    };
    let [ContractExpression::ResourceCount(resource)] = application.arguments.as_slice() else {
        return Err(shape());
    };
    let ResourceClause::Declared {
        name, arguments, ..
    } = resource.as_ref()
    else {
        return Err(shape());
    };
    if arguments.len() < 2
        || arguments
            .iter()
            .any(|argument| matches!(argument, ContractExpression::ResourceWildcard))
    {
        return Err(shape());
    }
    let values = arguments
        .iter()
        .map(|argument| {
            crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
                argument,
                assumptions,
                ContractEnvironment::new(context.values, context.array_refs)
                    .with_parameters(context.parameters),
                FixedStateFrame::new(
                    context.pre_state,
                    context.post_state,
                    context.result,
                    context.recorded_states,
                ),
                spec_definitions,
                &BTreeSet::new(),
            )
        })
        .collect::<Result<Vec<_>, _>>()
        .map_err(|message| {
            error(format!(
                "could not evaluate the member's arguments: {message}"
            ))
        })?;
    let theorem = crate::kernel::prove_population_member_count_zero(
        context.post_state,
        name,
        &values,
        assumptions,
    )
    .ok_or_else(|| {
        error(format!(
            "`count({name}(...))` and its population's count must each be one defined count at this state"
        ))
    })?;
    let crate::kernel::Proposition::Implies(guard, conclusion) = theorem.proposition() else {
        return Err(error(
            "the population law did not produce a guarded theorem".to_string(),
        ));
    };
    if preparing_application() {
        let mut population = resource.as_ref().clone();
        if let ResourceClause::Declared { arguments, .. } = &mut population {
            for argument in arguments.iter_mut().skip(1) {
                *argument = ContractExpression::ResourceWildcard;
            }
        }
        let surface = ClickProposition::Comparison {
            left: ContractExpression::ResourceCount(Box::new(population)),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::IntegerLiteral("0".into()),
        };
        crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
            ClickError::new("population theorem has a premise obligation")
                .with_spelled_requirement(
                    guard.as_ref().clone(),
                    surface,
                    "empty population".into(),
                ),
        )?;
    } else if !exact_fact_is_available(guard, available) {
        return Err(error(format!(
            "required exact fact is unavailable: the population's count is zero ({})",
            describe_pure_fact(guard, ParameterBinding::default())
        )));
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

pub(in crate::surface::proof) fn instantiate_generic_theorem_application_definition(
    definition: &TheoremDefinition,
    application: &TheoremApplication,
    assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<TheoremDefinition, String> {
    if application.arguments.len() != definition.parameters().len() {
        return Err(format!(
            "theorem `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            application.arguments.len()
        ));
    }
    if definition.type_parameters().is_empty() {
        return generics::instantiate_theorem_statement(definition, &BTreeMap::new());
    }
    // An `Integer` parameter decides no type argument, and its argument,
    // a loop's `iterations` for one, is no C expression to read a type from.
    let argument_types = application
        .arguments
        .iter()
        .zip(definition.parameters())
        .map(|(argument, parameter)| {
            if parameter.click_type() == &ClickType::Integer {
                return Ok(None);
            }
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
    if let Some((index, formats)) = pure_theorems::kernel_law_index_types(definition.name()) {
        let admitted = match substitution
            .get(index)
            .and_then(generics::TypeArgument::value)
        {
            Some(ClickType::Program(actual)) => formats
                .iter()
                .any(|allowed| allowed.to_kernel_type() == actual.to_kernel_type()),
            _ => false,
        };
        if !admitted {
            return Err(if matches!(
                definition.name(),
                "click::separation::contains_subrange"
                    | "click::separation::contains_element"
                    | "click::separation::contains_rebase"
                    | "click::separation::contains_joined_ranges"
                    | "click::separation::separate_adjacent_ranges"
            ) {
                "interval law bounds must be int32 or uint64"
            } else {
                "elements indices must be int32, int64, or uint64"
            }
            .into());
        }
    }
    let concrete = generics::instantiate_theorem_statement(definition, &substitution)?;
    if matches!(
        definition.name(),
        "click::separation::separate_elements"
            | "click::separation::distinct_elements"
            | "click::separation::contains_subrange"
            | "click::separation::contains_element"
            | "click::separation::contains_rebase"
            | "click::separation::contains_joined_ranges"
            | "click::separation::separate_adjacent_ranges"
    ) {
        let parameter = &concrete.parameters()[0];
        let element = parameter
            .interface_type()
            .pointee_type()
            .ok_or_else(|| "expected a sized pointer element".to_string())?;
        let width = match parameter.struct_name().filter(|_| !element.is_pointer()) {
            Some(name) => spec_definitions
                .struct_sizes
                .and_then(|sizes| sizes.get(name))
                .copied()
                .ok_or_else(|| format!("struct `{name}` has no known layout"))?,
            None => element.to_kernel_type().byte_width(),
        };
        if width == 0 {
            return Err("separation law requires a nonzero element width".into());
        }
    }
    Ok(concrete)
}

fn theorem_application_argument_type(
    argument: &ContractExpression,
    assumptions: &PureFactContext,
    context: &TheoremApplicationContext<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Option<ClickType>, String> {
    if let Some(cast_type) = generics::explicit_cast_click_type(argument) {
        return Ok(Some(cast_type));
    }
    // A call's declared/instantiated result is its logical type. A generic
    // identity can preserve a pointer's original object evidence while its
    // selected type is int32* or void*, just as an explicit cast can.
    if let ContractExpression::Call { name, arguments } = argument
        && let Some(function) = spec_definitions.functions.get(name)
        && arguments.len() == function.parameters().len()
    {
        let return_type = if function.type_parameters().is_empty() {
            function.return_type().clone()
        } else {
            let actual_types = arguments
                .iter()
                .zip(function.parameters())
                .map(|(argument, parameter)| {
                    if parameter.click_type() == &ClickType::Integer {
                        return Ok(None);
                    }
                    theorem_application_argument_type(
                        argument,
                        assumptions,
                        context,
                        spec_definitions,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let substitution = generics::infer_type_substitution(
                "function",
                function.name(),
                function.type_parameters(),
                function
                    .parameters()
                    .iter()
                    .map(|parameter| parameter.click_type().clone()),
                actual_types,
            )?;
            generics::instantiate_click_type(function.return_type(), &substitution)?
        };
        return Ok(Some(
            match (return_type.interface_type(), function.return_object_class()) {
                (Some(interface_type), Some(class)) => {
                    ClickType::from_object_pointer_class(interface_type, class)
                }
                _ => return_type,
            },
        ));
    }
    match argument {
        ContractExpression::AlgebraicVariable { algebraic_type, .. }
        | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
            return Ok(Some(ClickType::Algebraic(algebraic_type.clone())));
        }
        ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
            return Ok(Some(generics::click_type_from_program_value(value)));
        }
        ContractExpression::Binding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => {
            if let Some(value) = context.values.get(name) {
                return Ok(Some(generics::click_type_from_program_value(value)));
            }
        }
        _ => {}
    }

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
    if let Ok(value) = capture_fixed_state_algebraic_expression_with_values(
        argument,
        ContractEnvironment::new(context.values, context.array_refs)
            .with_parameters(context.parameters),
        algebraic_bindings,
        context.integer_values,
        FixedStateFrame::new(
            context.pre_state,
            context.post_state,
            context.result,
            context.recorded_states,
        ),
        spec_definitions,
    ) {
        return Ok(Some(generics::click_type_from_algebraic_value_type(
            &value.algebraic_type.value_type(),
        )));
    }

    let active_functions = BTreeSet::new();
    evaluate_native_theorem_argument(
        argument,
        context,
        assumptions,
        spec_definitions,
        &active_functions,
    )
    .map(|value| Some(generics::click_type_from_program_value(&value)))
}

// Native arguments can contain checked Integer conversions. Lower them in
// the caller's scope before binding the resulting C value to the callee.
fn evaluate_native_theorem_argument(
    argument: &ContractExpression,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: &BTreeSet<String>,
) -> Result<ProgramValue, String> {
    evaluate_retained_theorem_argument(
        argument,
        context,
        assumptions,
        spec_definitions,
        opaque_click_functions,
    )
    .map(crate::kernel::ExecutionValue::into_native)
}

fn evaluate_retained_theorem_argument(
    argument: &ContractExpression,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: &BTreeSet<String>,
) -> Result<crate::kernel::ExecutionValue, String> {
    let algebraic_values = contract_expression_referenced_names(argument)
        .into_iter()
        .filter_map(|name| {
            context
                .algebraic_values
                .get(&name)
                .cloned()
                .map(|value| (name, value))
        })
        .collect();
    capture_fixed_state_retained_expression_with_guards(
        argument,
        assumptions,
        ContractEnvironment::new(context.values, context.array_refs)
            .with_parameters(context.parameters),
        algebraic_values,
        context.integer_values,
        FixedStateFrame::new(
            context.pre_state,
            context.post_state,
            context.result,
            context.recorded_states,
        ),
        spec_definitions,
        opaque_click_functions,
    )
    .map(|(root, _)| crate::kernel::ExecutionValue::Shared(root))
}

pub(super) fn theorem_application_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<
    (
        ProgramValueBindings,
        ClickArrayRefs,
        BTreeMap<String, SpecAlgebraicExpression>,
        PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    ),
    String,
> {
    let active_functions = BTreeSet::new();
    let mut values = ProgramValueBindings::new();
    let mut array_refs = BTreeMap::new();
    let mut algebraic_values = BTreeMap::new();
    // Callee parameters are substituted simultaneously.  Keep the caller's
    // bindings as the immutable lookup environment, and accumulate the
    // resulting parameter bindings separately; otherwise an earlier callee
    // parameter can capture a later argument with the same spelling.
    let mut integer_values = PersistentBinderMap::default();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        if parameter.click_type() == &ClickType::Resource {
            if !matches!(argument, ContractExpression::Resource(_)) {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects Resource",
                    theorem.name(),
                    parameter.name()
                ));
            }
            continue;
        }
        if matches!(argument, ContractExpression::Resource(_)) {
            return Err(format!(
                "theorem `{}` parameter `{}` does not accept Resource",
                theorem.name(),
                parameter.name()
            ));
        }
        if parameter.click_type() == &ClickType::Integer {
            let value = match crate::surface::lowering::lower_contract_integer_to_spec(
                argument,
                context.integer_values,
            ) {
                Ok(value) => value,
                Err(_) => crate::kernel::SpecIntegerExpression::Term(
                    capture_fixed_state_integer_expression_with_guards(
                        argument,
                        context.integer_values,
                        assumptions,
                        ContractEnvironment::new(context.values, context.array_refs)
                            .with_parameters(context.parameters),
                        FixedStateFrame::new(
                            context.pre_state,
                            context.post_state,
                            context.result,
                            context.recorded_states,
                        ),
                        spec_definitions,
                        context.algebraic_values.clone(),
                    )?
                    .0,
                ),
            };
            integer_values = integer_values.with_inserted(parameter.name().to_string(), value);
            continue;
        }
        let Some(parameter_type) = parameter.click_type().interface_type() else {
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
                ContractEnvironment::new(context.values, context.array_refs)
                    .with_parameters(context.parameters),
                algebraic_bindings,
                context.integer_values,
                FixedStateFrame::new(
                    context.pre_state,
                    context.post_state,
                    context.result,
                    context.recorded_states,
                ),
                spec_definitions,
            )?;
            fn click_type_matches_algebraic_value_type(
                expected: &ClickType,
                actual: &crate::kernel::AlgebraicValueType,
            ) -> bool {
                match (expected, actual) {
                    (ClickType::Integer, crate::kernel::AlgebraicValueType::Integer) => true,
                    (
                        ClickType::Algebraic(expected),
                        crate::kernel::AlgebraicValueType::Parameter(name),
                    ) => {
                        (expected.rigid && expected.name == *name)
                            || generics::is_primitive_instance(name, expected)
                    }
                    (
                        expected @ ClickType::CObjectPointer { interface_type, .. },
                        crate::kernel::AlgebraicValueType::ObjectPointer(actual, class),
                    ) => {
                        interface_type.to_kernel_type() == *actual
                            && expected.pointer_object_class().as_ref() == Some(class)
                    }
                    (
                        ClickType::Program(expected),
                        crate::kernel::AlgebraicValueType::Program(actual)
                        | crate::kernel::AlgebraicValueType::ObjectPointer(actual, _),
                    ) => expected.to_kernel_type() == *actual,
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
            let primitive_matches = value.algebraic_type.rigid
                && generics::is_primitive_instance(&value.algebraic_type.name, expected_type);
            let type_matches = primitive_matches
                || value.algebraic_type.rigid == expected_type.rigid
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
            if preparing_application() {
                for guard in crate::kernel::algebraic_argument_evaluation_guards(
                    context.post_state,
                    &value,
                    Some(context.pre_state),
                    assumptions,
                )? {
                    crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                        ClickError::new("model theorem argument has an evaluation obligation")
                            .with_unresolved_requirement(&ProofObligation::verification_condition(
                                guard,
                            )),
                    )
                    .map_err(|error| error.message().to_owned())?;
                }
            }
            algebraic_values.insert(parameter.name().to_string(), value);
            continue;
        };
        // The C null pointer constant at a pointer-typed theorem parameter is
        // that pointer type's null value, exactly as at a pure function's
        // pointer parameter, so a whole-tree claim can be stated at the null
        // parent (`parent_consistent(t, 0)`).
        if crate::surface::lowering::argument_is_null_pointer_constant(argument, parameter_type) {
            let pointer = ProgramValue::typed_pointer(
                crate::kernel::Address::null(),
                parameter_type.to_kernel_type(),
            );
            if let Some(element_type) = click_array_element_type(parameter_type) {
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        point: context.post_state.program_point(),
                        pointer: crate::kernel::Address::null(),
                        element_type,
                    },
                );
            }
            values.insert(parameter.name().to_string(), pointer);
            continue;
        }
        if parameter_is_click_array_ref(parameter) {
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
            let (array_ref, pointer_value) = evaluate_fixed_state_array_ref_through_kernel(
                argument,
                assumptions,
                ContractEnvironment::new(context.values, context.array_refs)
                    .with_parameters(context.parameters),
                algebraic_bindings,
                context.integer_values,
                FixedStateFrame::new(
                    context.pre_state,
                    context.post_state,
                    context.result,
                    context.recorded_states,
                ),
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
            if !crate::surface::validation::array_ref_elements_compatible(
                array_ref.element_type,
                expected_element_type,
            ) {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    theorem.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            // An instantiated `T*` supplies a declared stride, not a nominal
            // original-object requirement. Its concrete body was checked with
            // declared-only pointer metadata, so binding grants no provenance.
            let value = if let Some(class) = parameter.pointer_object_class()
                && !theorem
                    .generic_pointer_parameters
                    .contains(parameter.name())
            {
                let mut value = evaluate_native_theorem_argument(
                    argument,
                    context,
                    assumptions,
                    spec_definitions,
                    &active_functions,
                )?;
                if !crate::kernel::refine_object_pointer_argument_using_facts(
                    &mut value,
                    &class,
                    context.post_state.memory(),
                    assumptions,
                ) {
                    return Err(format!(
                        "theorem `{}` parameter `{}` requires original object class `{class}` or null",
                        theorem.name(),
                        parameter.name()
                    ));
                }
                value.retag_pointer(parameter_type.to_kernel_type())
            } else {
                ProgramValue::Pointer(
                    pointer_value.with_type(expected_element_type.pointer_to().unwrap()),
                )
            };
            values.insert(parameter.name().to_string(), value);
            array_refs.insert(parameter.name().to_string(), array_ref);
        } else {
            let value = RetainedProgramValue::from(evaluate_retained_theorem_argument(
                argument,
                context,
                assumptions,
                spec_definitions,
                &active_functions,
            )?);
            let native = value.native_compat();
            if !program_value_matches_click_type(native, parameter_type) {
                let (naming_parameters, naming_arguments) =
                    crate::surface::diagnostics::value_naming_tables(context.values);
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {}, got `{}` of type `{}`",
                    theorem.name(),
                    parameter.name(),
                    describe_interface_type(parameter_type),
                    crate::surface::diagnostics::describe_program_value(
                        native,
                        ParameterBinding::new(&naming_parameters, &naming_arguments)
                    ),
                    crate::kernel::program_type_spelling(native.program_type())
                ));
            }
            values.insert_retained(parameter.name().to_string(), value);
        }
    }
    Ok((values, array_refs, algebraic_values, integer_values))
}

pub(super) fn theorem_application_pointer_element_widths(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> BTreeMap<String, u32> {
    theorem
        .parameters()
        .iter()
        .zip(&application.arguments)
        .filter_map(|(parameter, argument)| {
            // A numeric address is still a scalar argument. Importing its
            // source pointer's stride would make scalar addition look like
            // pointer arithmetic while lowering the instantiated clause.
            if !parameter_is_click_array_ref(parameter) {
                return None;
            }
            let declared_width = parameter.struct_name().and_then(|name| {
                if parameter
                    .interface_type()
                    .pointee_type()
                    .is_some_and(|ty| ty.is_pointer())
                {
                    parameter
                        .interface_type()
                        .pointee_type()
                        .map(|ty| ty.to_kernel_type().byte_width())
                } else {
                    spec_definitions
                        .struct_sizes
                        .and_then(|sizes| sizes.get(name))
                        .copied()
                }
            });
            declared_width
                .or_else(|| {
                    // A cast may retain the source object's provenance while
                    // changing the inferred element type. Generic instances
                    // use that element type's stride, not the source stride.
                    theorem
                        .generic_pointer_parameters
                        .contains(parameter.name())
                        .then(|| {
                            parameter
                                .interface_type()
                                .pointee_type()
                                .map(|ty| ty.to_kernel_type().byte_width())
                        })
                        .flatten()
                })
                .or_else(|| {
                    pointer_element_width_for_argument(argument, &context.pointer_element_widths)
                })
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
) -> BTreeMap<String, SpecPoint> {
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
                SpecPoint::At(array_ref.point.clone()),
            ))
        })
        .collect()
}

/// Read the element width of the expression substituted for a theorem
/// parameter. A scalar pointer cast supplies its target width even when it
/// preserves the source object's provenance.
fn pointer_element_width_for_argument(
    argument: &ContractExpression,
    known: &BTreeMap<String, u32>,
) -> Option<u32> {
    match argument {
        ContractExpression::MemoryLoad { value_type, .. } => {
            value_type.pointee_type().map(ProgramType::byte_width)
        }
        ContractExpression::Binding(name) | ContractExpression::ProgramBinding(name) => {
            known.get(name).copied()
        }
        ContractExpression::ProgramExpression(expression)
        | ContractExpression::CUnary {
            lowered: expression,
            ..
        }
        | ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => pointer_element_width_for_program_expression(expression, known),
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

fn pointer_element_width_for_program_expression(
    expression: &ProgramExpression,
    known: &BTreeMap<String, u32>,
) -> Option<u32> {
    match expression {
        ProgramExpression::Variable(name) => name.named_in(known).copied(),
        ProgramExpression::Add(left, right) => {
            pointer_element_width_for_program_expression(left, known)
                .or_else(|| pointer_element_width_for_program_expression(right, known))
        }
        ProgramExpression::Cast {
            target_type,
            pointee_struct: None,
            ..
        } if let Some(pointee) = target_type.pointee_type() => Some(pointee.byte_width()),
        ProgramExpression::Subtract(left, _)
        | ProgramExpression::PointerOffsetBytes { pointer: left, .. }
        | ProgramExpression::Subobject { pointer: left, .. }
        | ProgramExpression::Cast {
            expression: left, ..
        } => pointer_element_width_for_program_expression(left, known),
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

#[cfg(test)]
mod observed_integer_argument_tests {
    use super::*;

    #[test]
    fn integer_equality_citations_preserve_orientation_polarity_and_certificates() {
        let source = r#"
            theorem equal_arguments(a: Integer, b: Integer) {
                requires a == b;
                ensures a == b by { close(); }
            }
            theorem reverse_requirement(a: Integer, b: Integer) {
                requires b == a;
                ensures a == b by {
                    apply(equal_arguments(a, b));
                }
            }
            theorem reverse_citation(a: Integer, b: Integer) {
                requires b == a;
                ensures a == b by {
                    apply(equal_arguments(a, b));
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
                    apply(equal_arguments(to_integer(a), to_integer(b)));
                }
            }
        "#;
        verify_c_sources(source, &[]).unwrap();
        for label in [
            "reverse_requirement",
            "reverse_citation",
            "reverse_transport",
            "reverse_observations",
        ] {
            let expanded =
                expand_c_claim_source_by_label(source, &[], &format!("{label}.ensures_0")).unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
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
                verify_c_sources(&invalid, &[]).is_err(),
                "accepted {before} -> {after}"
            );
        }
    }

    #[test]
    fn pure_argument_obligations_reuse_ambient_evaluation_evidence() {
        let source = r#"
            theorem identity(value: int32) { ensures value == value by close(); }
            theorem use_argument(x: int32) {
                requires 0 <= x;
                requires x < 10;
                ensures x == x by { apply(identity(x + 1)); close(); }
            }
        "#;
        verify_c_sources(source, &[]).unwrap();
        let expanded =
            expand_c_claim_source_by_label(source, &[], "use_argument.ensures_0").unwrap();
        assert!(expanded.contains("apply(identity((x + 1)));"), "{expanded}");
        assert!(!expanded.contains("have "), "{expanded}");
        crate::surface::without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        assert!(verify_c_sources(&source.replace("requires x < 10;", ""), &[]).is_err());
    }

    #[test]
    fn machine_theorem_arguments_retain_domains_in_selected_expansion() {
        let source = r#"
            theorem reflexive(z: int32) { ensures z == z by close(); }
            theorem observed(x: int32) {
                requires defined(x + 1);
                ensures x == x by { apply(reflexive(x + 1)); close(); }
            }
        "#;
        verify_c_sources(source, &[]).unwrap();
        let expanded = expand_c_claim_source_by_label(source, &[], "observed.ensures_0").unwrap();
        crate::surface::without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
        let apply_start = expanded.find("apply(reflexive(").unwrap();
        let apply_end = apply_start + expanded[apply_start..].find(";\n").unwrap();
        assert!(
            !expanded[apply_start..apply_end].contains(" using {"),
            "{expanded}"
        );
        let erased = format!(
            "{} using {{}}{}",
            &expanded[..apply_end],
            &expanded[apply_end..]
        );
        assert!(crate::surface::without_implicit_solve(|| verify_c_sources(&erased, &[])).is_err());
        assert!(verify_c_sources(&source.replace("requires defined(x + 1);", ""), &[]).is_err());
    }

    #[test]
    fn integer_theorem_observed_arguments_preserve_types_guards_and_expansion() {
        let prefix = "theorem reflexive(z: Integer) { ensures z == z by close(); } ";
        for (ty, expression, guard) in [
            ("int32", "x + 1", "defined(x + 1)"),
            ("int64", "x + 1i64", "defined(x + 1i64)"),
            ("int128", "x / 3 as int128", "defined(x / 3 as int128)"),
        ] {
            let source = format!(
                "{prefix} theorem observed(x: {ty}) {{ requires {guard}; ensures to_integer({expression}) == to_integer({expression}) by {{ apply(reflexive(to_integer({expression}))); }} }}"
            );
            verify_c_sources(&source, &[])
                .unwrap_or_else(|error| panic!("{ty}: {}", error.message()));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "observed.ensures_0").unwrap();
            verify_c_sources(&expanded, &[]).unwrap();
            if ty != "int128" {
                let apply_start = expanded.find("apply(reflexive(").unwrap();
                let apply_end = apply_start + expanded[apply_start..].find(";\n").unwrap();
                assert!(
                    !expanded[apply_start..apply_end].contains(" using {"),
                    "{expanded}"
                );
                let erased = format!(
                    "{} using {{}}{}",
                    &expanded[..apply_end],
                    &expanded[apply_end..]
                );
                assert!(
                    verify_c_sources(&erased, &[]).is_err(),
                    "erased argument guard was accepted"
                );
                let missing = source.replace(&format!("requires {guard};"), "");
                assert!(verify_c_sources(&missing, &[]).is_err());
            }
        }
        for argument in [
            "to_integer(true)",
            "true",
            "to_integer(2147483647 + 1)",
            "truncating_quotient(to_integer(x), 0)",
            // `x / 0` is total, but `x / -1` overflows at `x == MIN`.
            "to_integer(x / -1)",
        ] {
            let source = format!(
                "{prefix} theorem refused(x: int32) {{ ensures x == x by {{ apply(reflexive({argument})); close(); }} }}"
            );
            let Err(error) = verify_c_sources(&source, &[]) else {
                panic!("invalid argument accepted: {argument}");
            };
            assert!(error.message().len() < 8000);
        }
    }

    #[test]
    fn model_theorem_arguments_retain_native_guards_in_expansion() {
        let source = r#"
spec enum Count { At(int32) }
function count(model: Count) -> int32 { match model { Count::At(value) => value, } }

theorem count_less(value: int32, model: Count) {
    requires to_integer(count(model)) == to_integer(value) - 1;
    ensures to_integer(count(model)) < to_integer(value) by {
        close() using { to_integer(count(model)) == to_integer(value) - 1; };
    }
}

theorem nested_count(value: int32) {
    requires defined(value - 1);
    ensures to_integer(count(Count::At(value - 1))) < to_integer(value) by {
        unfold(count(Count::At(value - 1)));
        have to_integer(value - 1) == to_integer(value) - 1;
        have to_integer(count(Count::At(value - 1))) == to_integer(value) - 1 by {
            rewrite(count(Count::At(value - 1)), value - 1); close();
        }
        apply(count_less(value, Count::At(value - 1)));
        close();
    }
}
"#;
        verify_c_sources(source, &[])
            .expect("nested model argument must retain its known overflow guard");
        let expanded =
            expand_c_claim_source_by_label(source, &[], "nested_count.ensures_0").unwrap();
        crate::surface::without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .expect("the explicit application must cold-check with its selected guard");
        let apply_start = expanded.find("apply(count_less(").unwrap();
        let apply_end = apply_start + expanded[apply_start..].find(";\n").unwrap();
        assert!(
            !expanded[apply_start..apply_end].contains(" using {"),
            "{expanded}"
        );
        let erased = format!(
            "{} using {{ to_integer(count(Count::At(value - 1))) == to_integer(value) - 1; }}{}",
            &expanded[..apply_end],
            &expanded[apply_end..]
        );
        assert!(
            crate::surface::without_implicit_solve(|| verify_c_sources(&erased, &[])).is_err(),
            "the theorem's requirement alone must not supply the argument's overflow guard"
        );
        let missing = source.replace("requires defined(value - 1);", "");
        assert!(verify_c_sources(&missing, &[]).is_err());
    }

    #[test]
    fn model_argument_guards_select_whole_definedness_facts_for_nested_fields_and_helpers() {
        for argument in [
            "Count::At(x + y)",
            "Count::Wrapped(Count::At(x + y))",
            "make_count(x + y)",
        ] {
            let source = format!(
                r#"
                spec enum Count {{ At(int32), Wrapped(Count) }}
                function make_count(value: int32) -> Count {{ Count::At(value) }}
                function count_value(model: Count) -> int32 decreases model {{
                    match model {{ Count::At(value) => value, Count::Wrapped(inner) => count_value(inner), }}
                }}
                theorem known_count(model: Count) {{
                    requires to_integer(count_value(model)) == 0;
                    ensures to_integer(count_value(model)) <= 0 by {{ close() using {{ to_integer(count_value(model)) == 0; }}; }}
                }}
                theorem guarded(x: int32, y: int32) {{
                    requires defined(x + y);
                    requires to_integer(count_value({argument})) == 0;
                    ensures to_integer(count_value({argument})) <= 0 by {{ apply(known_count({argument})); close(); }}
                }}
            "#
            );
            verify_c_sources(&source, &[]).unwrap_or_else(|error| panic!("{argument}: {error}"));
            let expanded =
                expand_c_claim_source_by_label(&source, &[], "guarded.ensures_0").unwrap();
            crate::surface::without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
            let apply_start = expanded.find("apply(known_count(").unwrap();
            let apply_end = apply_start + expanded[apply_start..].find(";\n").unwrap();
            assert!(
                !expanded[apply_start..apply_end].contains(" using {"),
                "{expanded}"
            );
            let erased = format!(
                "{} using {{ to_integer(count_value({argument})) == 0; }}{}",
                &expanded[..apply_end],
                &expanded[apply_end..]
            );
            assert!(
                crate::surface::without_implicit_solve(|| verify_c_sources(&erased, &[])).is_err(),
                "{argument}: accepted erased evaluation guards"
            );
        }
    }

    #[test]
    fn integer_theorem_arguments_capture_current_entry_state_and_result_values() {
        let parsed = crate::surface::parser::parse_file_items(
            "theorem reflexive(z: Integer) { ensures z == z by close(); }",
        )
        .unwrap();
        let theorem = &parsed.theorem_definitions()[0];
        let pre_state = ExecutionState::new().with_local("x", int32(7u32));
        let post_state = pre_state.clone().with_local("x", int32(9u32));
        let values = ProgramValueBindings::new();
        let arrays = BTreeMap::new();
        let algebraic = BTreeMap::new();
        let integers = PersistentBinderMap::default();
        let result = int32(11u32);
        let mut retained_states = RecordedStates::default();
        retained_states.insert(
            ProgramPointSelector::Mark("before".into()),
            pre_state.clone(),
        );
        let context = TheoremApplicationContext {
            parameters: ParameterBinding::default(),
            values: &values,
            array_refs: &arrays,
            algebraic_values: &algebraic,
            pre_state: &pre_state,
            post_state: &post_state,
            result: Some(&result),
            recorded_states: &retained_states,
            integer_values: &integers,
            pointer_element_widths: BTreeMap::new(),
        };
        let x = ContractExpression::Binding("x".into());
        for (argument, expected) in [
            (x.clone(), 9),
            (ContractExpression::Old(Box::new(x.clone())), 7),
            (
                ContractExpression::At {
                    selector: ProgramPointSelector::Mark("before".into()),
                    expression: Box::new(x),
                },
                7,
            ),
            (
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::CONTRACT_RESULT,
                )),
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

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/surface/proof/theorem_application/observed_integer_argument_tests.rs"
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

/// `proposition`, a clause of a theorem with `parameters`, with each native
/// comparison over machine-integer parameters stated by the observations it
/// compares wherever its instance has arithmetic: `0 <= value` at
/// `value = n - 1` instantiates to `0 <= to_integer(n - 1)`, the native
/// comparison it is, rather than `0 <= n - 1`, which reads as an Integer claim
/// where arithmetic is Integer. A clause comparing arithmetic over machine
/// parameters with no observation was read natively (a library module, whose
/// clauses are its kernel axioms), so `value - 1 < value` instantiates to
/// `to_integer(n - 1) < to_integer(n)`.
pub(in crate::surface::proof) fn observe_machine_parameters(
    proposition: &ClickProposition,
    parameters: &[FunctionParameter],
    substitutions: &BTreeMap<String, ContractExpression>,
) -> ClickProposition {
    fn arithmetic(expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Add(..)
            | ContractExpression::Subtract(..)
            | ContractExpression::Multiply(..) => true,
            ContractExpression::Negate(inner) => {
                !matches!(inner.as_ref(), ContractExpression::IntegerLiteral(_))
            }
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => arithmetic(inner),
            _ => false,
        }
    }
    let machine = parameters
        .iter()
        .filter(|parameter| {
            matches!(parameter.click_type(), ClickType::Program(interface_type)
                if crate::surface::integer_conversions::machine_integer_source_type(*interface_type))
        })
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    // A side the comparison reads natively: a machine parameter or a literal.
    let parameter = |side: &ContractExpression| match side {
        ContractExpression::Binding(name)
        | ContractExpression::ProgramBinding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) if machine.contains(name.as_str()) => Some(name.clone()),
        _ => None,
    };
    // A suffixed literal, such as `100u64`, is a machine constant: it reads
    // natively too, so `100u64 < value` at `value = n - k` is the native
    // comparison `to_integer(100u64) < to_integer(n - k)`, not
    // `100u64 < n - k`.
    let literal = |side: &ContractExpression| match side {
        ContractExpression::IntegerLiteral(_) => true,
        ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
            super::resources::is_integer_constant(value)
        }
        ContractExpression::Negate(inner) => {
            matches!(inner.as_ref(), ContractExpression::IntegerLiteral(_))
        }
        _ => false,
    };
    // Machine arithmetic over machine parameters and literals, the shape a
    // native comparison side has.
    fn tree(
        side: &ContractExpression,
        parameter: &dyn Fn(&ContractExpression) -> Option<String>,
        literal: &dyn Fn(&ContractExpression) -> bool,
    ) -> bool {
        match side {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                tree(left, parameter, literal) && tree(right, parameter, literal)
            }
            _ => parameter(side).is_some() || literal(side),
        }
    }
    let machine_tree = |side: &ContractExpression| tree(side, &parameter, &literal);
    let observe = |side: &ContractExpression| {
        if literal(side) && !matches!(side, ContractExpression::ProgramExpression(_)) {
            side.clone()
        } else {
            ContractExpression::Call {
                name: "to_integer".to_string(),
                arguments: vec![side.clone()],
            }
        }
    };
    fn walk(
        proposition: &ClickProposition,
        rewrite: &dyn Fn(&ClickProposition) -> Option<ClickProposition>,
    ) -> ClickProposition {
        if let Some(rewritten) = rewrite(proposition) {
            return rewritten;
        }
        let recurse = |inner: &ClickProposition| Box::new(walk(inner, rewrite));
        match proposition {
            ClickProposition::And(left, right) => {
                ClickProposition::And(recurse(left), recurse(right))
            }
            ClickProposition::Or(left, right) => {
                ClickProposition::Or(recurse(left), recurse(right))
            }
            ClickProposition::Implies(left, right) => {
                ClickProposition::Implies(recurse(left), recurse(right))
            }
            ClickProposition::Not(inner) => ClickProposition::Not(recurse(inner)),
            other => other.clone(),
        }
    }
    let rewrite = |proposition: &ClickProposition| {
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = proposition
        else {
            return None;
        };
        let sides = [left, right];
        let native = sides.iter().all(|side| machine_tree(side));
        let instance_arithmetic = sides.iter().any(|side| {
            arithmetic(side)
                || parameter(side)
                    .and_then(|name| substitutions.get(&name))
                    .is_some_and(arithmetic)
        });
        (native && instance_arithmetic).then(|| ClickProposition::Comparison {
            left: observe(left),
            operator: *operator,
            right: observe(right),
        })
    };
    walk(proposition, &rewrite)
}

/// Capture descriptors in the caller before substituting any callee name.
/// A descriptor carries no ownership, and later stores cannot change its value.
pub(super) fn theorem_resource_argument_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<BTreeMap<String, ContractExpression>, String> {
    let mut bindings = BTreeMap::new();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        if parameter.click_type() != &ClickType::Resource {
            continue;
        }
        let ContractExpression::Resource(subject) = argument else {
            return Err(format!("parameter `{}` expects Resource", parameter.name()));
        };
        let descriptor = ClickProposition::Contains {
            parent: subject.as_ref().clone(),
            child: subject.as_ref().clone(),
        };
        let lowered = lower_fixed_state_proposition_through_kernel_with(
            &descriptor,
            assumptions,
            ContractEnvironment::new(context.values, context.array_refs)
                .with_parameters(context.parameters),
            FixedStateFrame::new(
                context.pre_state,
                context.post_state,
                context.result,
                context.recorded_states,
            ),
            spec_definitions,
            FixedStateLoweringOptions {
                integer_values: Some(context.integer_values),
                algebraic_values: Some(context.algebraic_values),
                pointer_element_widths: context.pointer_element_widths.clone(),
                ..Default::default()
            },
        )?;
        let Proposition::ResourceContains { parent, .. } = lowered else {
            return Err("resource argument has unresolved span requirements".into());
        };
        bindings.insert(
            parameter.name().to_string(),
            ContractExpression::Resource(Box::new(ResourceSubject::Captured {
                value: *parent,
                source: subject.clone(),
            })),
        );
    }
    Ok(bindings)
}
