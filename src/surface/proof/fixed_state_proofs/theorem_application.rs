use super::*;
use crate::kernel::ExecutionFactSource;

pub(in crate::surface::proof) struct CheckedFixedStateTheoremApplication {
    pub(in crate::surface::proof) facts: ProofFacts,
    pub(in crate::surface::proof) added_facts: Vec<Proposition>,
    /// All conclusions this application checked, including already-stated ones.
    pub(in crate::surface::proof) checked_facts: Vec<Proposition>,
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
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    surface_propositions: &SurfacePropositionMap,
    unfolded_predicates: &[String],
    effect_facts: &(impl ExecutionFactSource + ?Sized),
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CheckedFixedStateTheoremApplication, ClickError> {
    let resource_facts = fixed_state
        .state
        .resources()
        .observable_facts_assuming_valid(available.assumptions());
    let mut lowering_assumptions = available.assumptions().clone();
    for fact in resource_facts {
        lowering_assumptions = lowering_assumptions.assume_proposition(fact);
    }

    if crate::surface::proof::theorem_application::preparing_application() {
        lowering_assumptions = lowering_assumptions.retaining_argument_obligations();
    }

    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let freshly_lowered = lower_fixed_state_proposition_with_integer_values(
            surface_premise,
            &lowering_assumptions,
            parameter_binding,
            fixed_state,
            integer_values,
            spec_definitions,
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
        // A listed premise the lowering folded to a ground constant needs no
        // fact when that constant is the value it asserts: `0 <= 0` at an
        // instance is `true is true`, and the availability check below
        // accepts it by the rule every `using` list shares
        // (`listed_premise_holds`), which also accepts an equality listed in
        // the other orientation from the fact held.
        if !available.listed_premise_available(&premise, &[], true) {
            let available_facts = available.to_vec();
            // Name the listed premise in the reader's own spelling: a
            // premise lowered to a constant or to an internal term says
            // neither which `using` entry was refused nor why.
            let constant_note = match &premise {
                Proposition::ConditionIs(ConditionTerm::Constant(_), _) => {
                    " (it is false at this instance)"
                }
                _ => "",
            };
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `apply using` requires an exact premise: listed premise `{}`{constant_note} is not an available fact: {}",
                crate::surface::diagnostics::describe_click_proposition(surface_premise),
                describe_missing_pure_fact(
                    &premise,
                    &available_facts,
                    fixed_state.state.resources().facts(),
                    parameter_binding,
                    effect_facts,
                )
            )));
        }
        // Citing a stated range cites both of its halves; see
        // `cite_range_extent_guards`.
        crate::surface::proof::theorem_application::cite_range_extent_guards(
            &premise,
            &mut explicit_premises,
            |guard| available.available_across_effects(guard, &[]),
        );
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }

    // The application reads the caller's environment only through its
    // arguments, so it needs only the names they mention.
    let mut names = BTreeSet::new();
    for argument in &application.arguments {
        crate::surface::lowering::collect_contract_expression_referenced_names(
            argument, &mut names,
        );
    }
    let (values, array_refs) =
        contract_environment_for_names(parameter_binding, &names, fixed_state.state).map_err(
            |error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: {}",
                    error.message
                ))
            },
        )?;
    let application_context = TheoremApplicationContext {
        values: &values,
        array_refs: &array_refs,
        algebraic_values,
        pre_state: fixed_state.pre_state,
        post_state: fixed_state.state,
        result: fixed_state.result,
        recorded_states: fixed_state.recorded_states,
        integer_values,
        pointer_element_widths: parameter_pointer_element_widths_named(parameter_binding, &names),
    };
    let conclusions = instantiate_theorem_application_with_assumptions(
        theorem_environment,
        application,
        claim_label,
        None,
        tactic_index,
        &explicit_premises,
        &lowering_assumptions,
        &application_context,
        spec_definitions,
        unfolded_predicates,
    )?;

    let mut facts = available.clone();
    let mut added_facts = Vec::new();
    for conclusion in &conclusions {
        if !facts.contains_top_level(conclusion) {
            added_facts.push(conclusion.clone());
        }
        facts = facts.with_kernel_checked_fact(conclusion.clone());
    }

    Ok(CheckedFixedStateTheoremApplication {
        facts,
        added_facts,
        checked_facts: conclusions,
    })
}

/// Lowers one application's requirements against an already-persistent
/// assumption context. Smart proof-object queries use this entry point so
/// choosing a candidate does not materialize or rescan every ambient fact.
pub(in crate::surface::proof) fn lower_theorem_application_requirements_with_assumptions(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, String> {
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        format!(
            "unknown theorem `{}`{}",
            application.name,
            crate::surface::validation::library_import_hint(&application.name)
        )
    })?;
    let theorem = instantiate_generic_theorem_application_definition(
        theorem,
        application,
        assumptions,
        context,
        spec_definitions,
    )?;
    let (values, array_refs, algebraic_values, integer_values) = theorem_application_bindings(
        &theorem,
        application,
        context,
        assumptions,
        spec_definitions,
    )?;
    let resource_bindings = super::super::theorem_application::theorem_resource_argument_bindings(
        &theorem,
        application,
        context,
        assumptions,
        spec_definitions,
    )?;
    // The theorem's parameters shadow any C local of the same name: the
    // application binds them, not the state.
    let bind = |state: &ExecutionState| {
        values.iter().fold(state.clone(), |state, (name, value)| {
            state.with_local(name.clone(), value.clone())
        })
    };
    let pre_state = bind(context.pre_state);
    let post_state = bind(context.post_state);
    let bound_array_memories =
        super::super::theorem_application::theorem_application_bound_array_memories(
            &theorem,
            application,
            &array_refs,
        );
    crate::surface::proof::pure_theorems::theorem_requirement_propositions(&theorem)
        .map_err(|error| error.message)?
        .iter()
        .map(|requirement| {
            let requirement = substitute_click_proposition(requirement, &resource_bindings)?;
            let pointer_element_widths =
                super::super::theorem_application::theorem_application_pointer_element_widths(
                    &theorem,
                    application,
                    context,
                    spec_definitions,
                );
            let lowered = lower_fixed_state_proposition_through_kernel_with(
                &requirement,
                assumptions,
                ContractEnvironment::new(&values, &array_refs),
                FixedStateFrame::new(&pre_state, &post_state, None, context.recorded_states),
                spec_definitions,
                FixedStateLoweringOptions {
                    algebraic_values: Some(&algebraic_values),
                    integer_values: Some(&integer_values),
                    bound_array_memories: Some(&bound_array_memories),
                    pointer_element_widths,
                    ..Default::default()
                },
            )?;
            unfold_predicates_in_proposition(
                spec_definitions,
                unfolded_predicates,
                &lowered,
                assumptions,
            )
        })
        .collect()
}
