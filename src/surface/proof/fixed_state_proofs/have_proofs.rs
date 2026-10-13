use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

struct IterativeSpecPropositionDrop(Option<SpecProposition>);

impl IterativeSpecPropositionDrop {
    fn new(proposition: SpecProposition) -> Self {
        Self(Some(proposition))
    }

    fn as_ref(&self) -> &SpecProposition {
        self.0.as_ref().expect("the proposition guard is live")
    }
}

impl Drop for IterativeSpecPropositionDrop {
    fn drop(&mut self) {
        let Some(proposition) = self.0.take() else {
            return;
        };
        drop_spec_proposition_iteratively(proposition);
    }
}

fn drop_spec_proposition_iteratively(proposition: SpecProposition) {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            SpecProposition::And(left, right)
            | SpecProposition::Or(left, right)
            | SpecProposition::Implies(left, right) => {
                pending.push(*right);
                pending.push(*left);
            }
            SpecProposition::Not(body)
            | SpecProposition::ForAllMachineInteger { body, .. }
            | SpecProposition::ForAllInt32 { body, .. }
            | SpecProposition::ForAllInteger { body, .. }
            | SpecProposition::ForAllAlgebraic { body, .. }
            | SpecProposition::ForAllPointer { body, .. }
            | SpecProposition::ExistsMachineInteger { body, .. }
            | SpecProposition::ExistsInt32 { body, .. }
            | SpecProposition::ExistsInteger { body, .. }
            | SpecProposition::ExistsAlgebraic { body, .. }
            | SpecProposition::ExistsPointer { body, .. } => pending.push(*body),
            proposition => drop(proposition),
        }
    }
}

pub(in crate::surface::proof) fn lower_fixed_state_proposition(
    proposition: &ClickProposition,
    available: &[Proposition],
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let assumptions = assumptions_from_propositions(available);
    lower_fixed_state_proposition_with_assumptions(
        proposition,
        &assumptions,
        parameter_binding,
        fixed_state,
        spec_definitions,
    )
}

/// Lowers one proposition against a fixed symbolic C state and an already-indexed fact context.
///
/// `Proof` keeps this context persistent and incrementally updated, so a
/// local step does not rebuild it by scanning every unrelated fact. Legacy
/// vector callers continue through `lower_fixed_state_proposition` above.
pub(in crate::surface::proof) fn lower_fixed_state_proposition_with_assumptions(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_with_assumptions_recording_introductions(
        proposition,
        assumptions,
        parameter_binding,
        fixed_state,
        spec_definitions,
    )
    .map(|(proposition, _)| proposition)
}

/// Fixed-state lowering with the exact algebraic proof locals referenced by
/// the written proposition. Algebraic `choose` bindings live outside C state,
/// so callers pass them explicitly just as Integer proof locals are passed by
/// the companion helper below.
pub(in crate::surface::proof) fn lower_fixed_state_proposition_with_algebraic_values(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let values = parameter_values(parameter_binding).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(
        parameter_binding.parameters,
        &values,
        fixed_state.state.memory(),
    );
    let (values, array_refs) =
        contract_environment_at_state(&values, &array_refs, fixed_state.state);
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        fixed_state,
        spec_definitions,
        FixedStateLoweringOptions {
            algebraic_values: Some(algebraic_values),
            integer_values: Some(integer_values),
            pointer_element_widths: parameter_pointer_element_widths(parameter_binding.parameters),
            ..Default::default()
        },
    )
}

/// Lowers a fixed-state proposition while retaining checked mathematical
/// Integer bindings introduced by the surrounding theorem or proof scope.
/// The ordinary helper remains the default for C-only propositions; this path
/// is used when a fold law's explicit guard names an Integer binding.
pub(in crate::surface::proof) fn lower_fixed_state_proposition_with_integer_values(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let values = parameter_values(parameter_binding).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(
        parameter_binding.parameters,
        &values,
        fixed_state.state.memory(),
    );
    let (values, array_refs) =
        contract_environment_at_state(&values, &array_refs, fixed_state.state);
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        fixed_state,
        spec_definitions,
        FixedStateLoweringOptions {
            integer_values: Some(integer_values),
            pointer_element_widths: parameter_pointer_element_widths(parameter_binding.parameters),
            ..Default::default()
        },
    )
}

/// [`lower_fixed_state_proposition_with_assumptions`], also returning the
/// head chain the kernel recorded for the lowered proposition.
pub(in crate::surface::proof) fn lower_fixed_state_proposition_with_assumptions_recording_introductions(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(Proposition, crate::kernel::LoweringIntroductions), String> {
    let values = parameter_values(parameter_binding).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(
        parameter_binding.parameters,
        &values,
        fixed_state.state.memory(),
    );
    let (values, array_refs) =
        contract_environment_at_state(&values, &array_refs, fixed_state.state);
    lower_fixed_state_proposition_through_kernel_with_introductions(
        proposition,
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        fixed_state,
        spec_definitions,
        FixedStateLoweringOptions {
            pointer_element_widths: parameter_pointer_element_widths(parameter_binding.parameters),
            ..Default::default()
        },
    )
}

/// The one lowering of a proof-side proposition: elaborated into the
/// kernel's spec form like a contract clause and lowered by the kernel at
/// the proof's state, so it is spelled exactly as the contract's clauses
/// and the execution's facts are. The state carries the parameters at
/// their entry values, the proof-local bindings, and `result`.
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        assumptions,
        contract_environment,
        fixed_state,
        spec_definitions,
        FixedStateLoweringOptions::default(),
    )
}

/// What a fixed-state lowering reads beyond the state, the facts, and the
/// contract environment. Every field defaults to empty.
#[derive(Default)]
pub(in crate::surface) struct FixedStateLoweringOptions<'a> {
    /// Algebraic proof locals the written proposition names.
    pub(in crate::surface) algebraic_values: Option<&'a BTreeMap<String, SpecAlgebraicExpression>>,
    /// Checked mathematical Integer bindings of the surrounding scope.
    pub(in crate::surface) integer_values:
        Option<&'a crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>>,
    /// Array-valued names bound to array references of their own, as a theorem
    /// application binds its parameters. An argument that names another state
    /// (`old(a)`, `at(mark, a)`) binds the parameter to that state's memory;
    /// one read at the lowering state is absent and reads through it.
    pub(in crate::surface) bound_array_memories: Option<&'a BTreeMap<String, SpecMemory>>,
    /// Click functions that stay applications: the proof unfolds them itself.
    pub(in crate::surface) opaque_click_functions: Option<&'a BTreeSet<String>>,
    pub(in crate::surface) pointer_element_widths: BTreeMap<String, u32>,
    /// The facts the lowering's obligations are checked against, when they
    /// differ from the facts it lowers under.
    pub(in crate::surface) obligation_assumptions: Option<&'a PureFactContext>,
}

/// [`lower_fixed_state_proposition_through_kernel_with_facts`], keeping only
/// the lowered proposition.
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
    options: FixedStateLoweringOptions<'_>,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel_with_facts(
        proposition,
        assumptions,
        contract_environment,
        fixed_state,
        spec_definitions,
        options,
    )
    .map(|(proposition, _, _)| proposition)
}

/// [`lower_fixed_state_proposition_through_kernel_with_facts`], also keeping
/// the head chain the kernel recorded for the proposition it produced. A
/// newly stated goal keeps that record so an introduction knows which of its
/// outermost nodes lowering inserted and which written binder each universal
/// bound.
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with_introductions(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
    options: FixedStateLoweringOptions<'_>,
) -> Result<(Proposition, crate::kernel::LoweringIntroductions), String> {
    lower_fixed_state_proposition_through_kernel_with_facts(
        proposition,
        assumptions,
        contract_environment,
        fixed_state,
        spec_definitions,
        options,
    )
    .map(|(proposition, introductions, _)| (proposition, introductions))
}

/// The kernel lowering of a proof-side proposition at a fixed state, with the
/// head chain it recorded and the facts lowering established.
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with_facts(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
    options: FixedStateLoweringOptions<'_>,
) -> Result<
    (
        Proposition,
        crate::kernel::LoweringIntroductions,
        Vec<Proposition>,
    ),
    String,
> {
    let no_integer_values = crate::persistent::PersistentMap::default();
    let FixedStateLoweringOptions {
        algebraic_values,
        integer_values,
        bound_array_memories,
        opaque_click_functions,
        pointer_element_widths,
        obligation_assumptions,
    } = options;
    let integer_values = integer_values.unwrap_or(&no_integer_values);
    let obligation_assumptions = obligation_assumptions.unwrap_or(assumptions);
    let mut click_function_calls = BTreeSet::new();
    crate::surface::validation::collect_click_function_calls_in_proposition(
        proposition,
        &mut click_function_calls,
    );
    let symbolic_load_assumptions =
        (!click_function_calls.is_empty()).then(|| assumptions.clone().keep_spec_loads_symbolic());
    let assumptions = symbolic_load_assumptions.as_ref().unwrap_or(assumptions);
    let states = FixedStateLowering::for_proposition(
        proposition,
        contract_environment,
        fixed_state.pre_state,
        fixed_state.state,
        fixed_state.result,
    );
    let spec = crate::surface::lowering::elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
        proposition,
        states.element_types,
        bound_array_memories.cloned().unwrap_or_default(),
        &states.entry_state,
        states.entry_values,
        states.current_values,
        algebraic_values.cloned().unwrap_or_default(),
        integer_values,
        fixed_state.result,
        fixed_state.recorded_snapshots,
        spec_definitions,
        opaque_click_functions.cloned().unwrap_or_default(),
        pointer_element_widths,)?;
    let spec = IterativeSpecPropositionDrop::new(spec);
    let (lowered, facts, obligations, introductions) =
        crate::kernel::c_lower_spec_proposition_with_checked_obligations(
            &states.lowering_state,
            spec.as_ref(),
            Some(&states.entry_state),
            assumptions,
        )
        .map_err(|refusal| match &refusal.dropped_fold_body {
            // The kernel pruned the only lowering of a range fold. It knows
            // which check fired and what it was about; only the surface can
            // say so in the names the reader wrote.
            Some(dropped) => describe_dropped_fold_body(
                dropped,
                obligation_assumptions,
                &StatedSite::new(
                    StatedForm::Proposition(proposition),
                    fixed_state.state,
                    contract_environment.values,
                ),
            ),
            None => refusal.message,
        })?;
    refuse_impossible_loads(
        &obligations
            .iter()
            .map(|obligation| obligation.proposition().clone())
            .collect::<Vec<_>>(),
        obligation_assumptions,
    )?;
    refuse_unproved_conversion_bounds(
        &obligations,
        obligation_assumptions,
        &StatedSite::new(
            StatedForm::Proposition(proposition),
            fixed_state.state,
            contract_environment.values,
        ),
    )?;
    Ok((lowered, introductions, facts))
}

/// The one evaluation of a proof-side expression: elaborated into the
/// kernel's spec form like a contract expression and evaluated by the kernel
/// at the proof's state. Calls named in `opaque_click_functions` stay
/// applications: the proof unfolds them itself.
pub(in crate::surface) fn evaluate_fixed_state_expression_through_kernel(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: &std::collections::BTreeSet<String>,
) -> Result<CValue, String> {
    evaluate_fixed_state_expression_through_kernel_with_algebraic_values(
        expression,
        assumptions,
        contract_environment,
        BTreeMap::new(),
        fixed_state,
        spec_definitions,
        opaque_click_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn evaluate_fixed_state_expression_through_kernel_with_algebraic_values(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: &std::collections::BTreeSet<String>,
) -> Result<CValue, String> {
    let mut click_function_calls = BTreeSet::new();
    crate::surface::validation::collect_click_function_calls(expression, &mut click_function_calls);
    let symbolic_load_assumptions =
        (!click_function_calls.is_empty()).then(|| assumptions.clone().keep_spec_loads_symbolic());
    let assumptions = symbolic_load_assumptions.as_ref().unwrap_or(assumptions);
    let states = FixedStateLowering::new(
        contract_environment,
        fixed_state.pre_state,
        fixed_state.state,
        fixed_state.result,
    );
    let spec = crate::surface::lowering::elaborate_fixed_state_expression_with_algebraic_values(
        expression,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        algebraic_values,
        fixed_state.result,
        fixed_state.recorded_snapshots,
        spec_definitions,
        opaque_click_functions.clone(),
        BTreeMap::new(),
    )?;
    let (value, obligations) = crate::kernel::c_evaluate_spec_expression_with_checked_obligations(
        &states.lowering_state,
        &spec,
        Some(&states.entry_state),
        assumptions,
    )?;
    refuse_unproved_conversion_bounds(
        &obligations,
        assumptions,
        &StatedSite::new(
            StatedForm::Expression(expression),
            fixed_state.state,
            contract_environment.values,
        ),
    )?;
    let obligations = obligations
        .iter()
        .map(|obligation| obligation.proposition().clone())
        .collect::<Vec<_>>();
    refuse_impossible_loads(&obligations, assumptions)?;
    Ok(value)
}

/// Capture one proof-side Integer expression as the symbolic term it denotes
/// at the current fixed state. Evaluation is intentionally checked here: any
/// conversion or machine arithmetic needed to form the argument must already
/// be justified by the supplied proof assumptions. Heap observations use the
/// existing logical specification read semantics and grant no access authority.
pub(in crate::surface::proof) fn capture_fixed_state_integer_expression(
    expression: &ContractExpression,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<crate::kernel::IntegerTerm, String> {
    capture_fixed_state_integer_expression_with_guards(
        expression,
        integer_values,
        assumptions,
        contract_environment,
        fixed_state,
        spec_definitions,
    )
    .map(|(value, _)| value)
}

pub(in crate::surface::proof) fn capture_fixed_state_integer_expression_with_guards(
    expression: &ContractExpression,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(crate::kernel::IntegerTerm, Vec<Proposition>), String> {
    let states = FixedStateLowering::for_expression(
        expression,
        contract_environment,
        fixed_state.pre_state,
        fixed_state.state,
        fixed_state.result,
    );
    let spec =
        crate::surface::lowering::elaborate_fixed_state_integer_expression_with_integer_values(
            expression,
            states.element_types,
            &states.entry_state,
            states.entry_values,
            states.current_values,
            integer_values,
            fixed_state.result,
            fixed_state.recorded_snapshots,
            spec_definitions,
            BTreeSet::new(),
            BTreeMap::new(),
        )?;
    crate::kernel::capture_spec_integer_value_with_guards(
        fixed_state.state,
        &spec,
        Some(fixed_state.pre_state),
        assumptions,
    )
    .map_err(|refusal| {
        let (names, arguments) =
            crate::surface::diagnostics::value_naming_tables(contract_environment.values);
        let mut labels = crate::surface::proof_diagnostics::render::SnapshotLabels::naming(
            ParameterBinding::new(&names, &arguments),
        );
        crate::surface::proof_diagnostics::render::describe_spec_capture_refusal_labeled(
            &refusal,
            &mut labels,
        )
    })
}

/// Captures an algebraic expression as the symbolic spec term it denotes at
/// this proof state. The kernel will evaluate the captured term together with
/// the theorem clause that consumes it.
pub(in crate::surface) fn capture_fixed_state_algebraic_expression(
    expression: &ContractExpression,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<SpecAlgebraicExpression, String> {
    capture_fixed_state_algebraic_expression_with_values(
        expression,
        contract_environment,
        BTreeMap::new(),
        fixed_state,
        spec_definitions,
    )
}

pub(in crate::surface) fn capture_fixed_state_algebraic_expression_with_values(
    expression: &ContractExpression,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<SpecAlgebraicExpression, String> {
    let states = FixedStateLowering::new(
        contract_environment,
        fixed_state.pre_state,
        fixed_state.state,
        fixed_state.result,
    );
    crate::surface::lowering::elaborate_fixed_state_algebraic_expression(
        expression,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        algebraic_values,
        fixed_state.result,
        fixed_state.recorded_snapshots,
        spec_definitions,
        BTreeSet::new(),
        BTreeMap::new(),
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn capture_fixed_state_algebraic_value(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    pre_state: &CState,
    state: &CState,
    snapshots: &RecordedSnapshots,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<crate::kernel::AlgebraicTerm, String> {
    let states = FixedStateLowering::new(contract_environment, pre_state, state, None);
    let spec = crate::surface::lowering::elaborate_fixed_state_algebraic_expression(
        expression,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        algebraic_values,
        None,
        snapshots,
        spec_definitions,
        BTreeSet::new(),
        BTreeMap::new(),
    )?;
    crate::kernel::capture_spec_algebraic_value(
        &states.lowering_state,
        &spec,
        Some(&states.entry_state),
        assumptions,
    )
}

/// Fold initializers create values, not new hypotheses: discharge every
/// evaluation obligation here, including reads in constructor arguments.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn capture_resource_field_initializer(
    expression: &ContractExpression,
    ty: &crate::kernel::ResourceFieldType,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    pre_state: &CState,
    state: &CState,
    snapshots: &RecordedSnapshots,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<crate::kernel::AlgebraicValue, String> {
    let states = FixedStateLowering::new(contract_environment, pre_state, state, None);
    match ty {
        crate::kernel::ResourceFieldType::C(expected) => {
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                expression,
                states.element_types,
                &states.entry_state,
                states.entry_values,
                states.current_values,
                None,
                snapshots,
                spec_definitions,
                BTreeSet::new(),
                BTreeMap::new(),
            )?;
            let (value, obligations) =
                crate::kernel::c_evaluate_spec_expression_with_checked_obligations(
                    &states.lowering_state,
                    &spec,
                    Some(&states.entry_state),
                    assumptions,
                )?;
            if obligations
                .iter()
                .any(|o| !assumptions.proves(o.proposition()))
            {
                return Err("fold initializer has unproved evaluation obligations".into());
            }
            if value.c_type() != *expected {
                return Err("fold initializer has the wrong type".into());
            }
            Ok(crate::kernel::AlgebraicValue::C(value))
        }
        crate::kernel::ResourceFieldType::Integer => {
            let spec = crate::surface::lowering::elaborate_fixed_state_integer_expression(
                expression,
                states.element_types,
                &states.entry_state,
                states.entry_values,
                states.current_values,
                None,
                snapshots,
                spec_definitions,
                BTreeSet::new(),
            )?;
            crate::kernel::capture_spec_integer_value(
                &states.lowering_state,
                &spec,
                Some(&states.entry_state),
                assumptions,
            )
            .map(crate::kernel::AlgebraicValue::Integer)
            .map_err(|refusal| {
                crate::surface::proof_diagnostics::render::describe_spec_capture_refusal(&refusal)
            })
        }
        crate::kernel::ResourceFieldType::Algebraic(_) => {
            let spec = crate::surface::lowering::elaborate_fixed_state_algebraic_expression(
                expression,
                states.element_types,
                &states.entry_state,
                states.entry_values,
                states.current_values,
                BTreeMap::new(),
                None,
                snapshots,
                spec_definitions,
                BTreeSet::new(),
                BTreeMap::new(),
            )?;
            crate::kernel::capture_spec_algebraic_value(
                &states.lowering_state,
                &spec,
                Some(&states.entry_state),
                assumptions,
            )
            .map(crate::kernel::AlgebraicValue::Algebraic)
        }
    }
}

/// The one evaluation of a C fragment stated outside a proof: a resource
/// clause's quantity, argument, or segment bound, an effect footprint, a
/// resource definition's read. The fragment is elaborated like any contract
/// expression and evaluated by the kernel at `state`, with `values` bound
/// where the state does not bind the name. A load the state does not
/// justify is refused unless `assumptions` allow symbolic contract loads, in
/// which case the load stays the symbolic term kernel execution spells it
/// as, and certification discharges its loadability from the path's facts.
pub(in crate::surface) fn evaluate_c_fragment_through_kernel(
    expression: &CExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CValue, String> {
    evaluate_c_fragment_with_binding_policy(
        expression,
        assumptions,
        contract_environment,
        state,
        result,
        false,
        None,
    )
}

/// Resource clauses use stable logical arguments even after the C parameter
/// changes; static addresses and memory still belong to the exact frontier.
pub(in crate::surface) fn evaluate_resource_fragment_through_kernel(
    expression: &CExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CValue, String> {
    evaluate_c_fragment_with_binding_policy(
        expression,
        assumptions,
        contract_environment,
        state,
        result,
        true,
        None,
    )
}

pub(in crate::surface) fn evaluate_resource_argument_through_kernel(
    original: &ContractExpression,
    lowered: &CExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CValue, String> {
    // Most resource fragments already carry their resolved C spelling.
    // Retain the source expression only where its `c(result)` distinction
    // matters, and keep the typed null supplied by parameter lowering.
    let original = if result.is_none()
        || !crate::surface::lowering::contract_expression_referenced_names(original)
            .contains("result")
        || matches!(lowered, CExpression::Value(CValue::Pointer(pointer)) if pointer.is_null())
    {
        None
    } else {
        Some(original)
    };
    evaluate_c_fragment_with_binding_policy(
        lowered,
        assumptions,
        contract_environment,
        state,
        result,
        true,
        original,
    )
}

#[allow(clippy::too_many_arguments)]
fn evaluate_c_fragment_with_binding_policy(
    expression: &CExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    state: &CState,
    result: Option<&CValue>,
    logical_arguments: bool,
    original: Option<&ContractExpression>,
) -> Result<CValue, String> {
    let fragment = ContractExpression::CFragment(expression.clone());
    let elaborated = original.unwrap_or(&fragment);
    // Bind only the names the fragment reads: a contract evaluates one
    // fragment per clause, and binding every value in scope for each would
    // make a contract with many parameters quadratic.
    let mut states =
        FixedStateLowering::for_expression(elaborated, contract_environment, state, state, result);
    if logical_arguments {
        for name in crate::surface::lowering::contract_expression_referenced_names(elaborated) {
            if let Some(value) = contract_environment.values.get(&name) {
                states.entry_values.insert(name.clone(), value.clone());
                states.current_values.insert(name, value.clone());
            }
        }
    }
    let spec = crate::surface::lowering::elaborate_fixed_state_expression(
        elaborated,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        result,
        &RecordedSnapshots::new(),
        SpecDefinitions::new(
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
        ),
        std::collections::BTreeSet::new(),
        BTreeMap::new(),
    )?;
    let (value, obligations) =
        crate::kernel::c_evaluate_spec_resource_expression_with_checked_obligations(
            &states.lowering_state,
            &spec,
            Some(&states.entry_state),
            assumptions,
        )?;
    refuse_unproved_conversion_bounds(
        &obligations,
        assumptions,
        &StatedSite::new(
            StatedForm::CFragment(expression),
            state,
            contract_environment.values,
        ),
    )?;
    let obligations = obligations
        .iter()
        .map(|obligation| obligation.proposition().clone())
        .collect::<Vec<_>>();
    refuse_impossible_loads(&obligations, assumptions)?;
    if !assumptions.should_allow_symbolic_contract_loads()
        && let Some(obligation) = obligations.iter().find(|obligation| {
            !crate::kernel::c_state_justifies_loadability_obligation(
                &states.lowering_state,
                obligation,
                assumptions,
            )
        })
    {
        return Err(crate::surface::diagnostics::describe_missing_pure_fact(
            obligation,
            &[],
            &[],
            ParameterBinding::default(),
            &[],
        ));
    }
    Ok(value)
}

/// The array reference a proof-side expression names: a parameter's own
/// reference when the expression is that name, otherwise the pointer the
/// kernel evaluates the expression to, in the memory of the state the
/// expression reads (`old(...)` the entry, `at(...)` its snapshot), with the
/// element type the expression's array reference declares.
pub(in crate::surface) fn evaluate_fixed_state_array_ref_through_kernel(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    fixed_state: FixedStateFrame<'_>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<ClickArrayRef, String> {
    if let ContractExpression::Binding(name)
    | ContractExpression::CFragment(CExpression::Variable(name))
    | ContractExpression::CBinding(name) = expression
        && let Some(array_ref) = contract_environment.array_refs.get(name)
    {
        return Ok(array_ref.clone());
    }
    let value = evaluate_fixed_state_expression_through_kernel(
        expression,
        assumptions,
        contract_environment,
        fixed_state,
        spec_definitions,
        &std::collections::BTreeSet::new(),
    )?;
    let CValue::Pointer(pointer) = value else {
        return Err(format!(
            "array reference expression did not evaluate to a pointer: `{}`",
            crate::surface::diagnostics::describe_c_value(&value, ParameterBinding::default())
        ));
    };
    let memory = match expression {
        ContractExpression::Old(_) => fixed_state.pre_state.memory().clone(),
        ContractExpression::At { selector, .. } => selected_snapshot_state(
            selector,
            fixed_state.pre_state,
            fixed_state.recorded_snapshots,
        )?
        .memory()
        .clone(),
        _ => fixed_state.state.memory().clone(),
    };
    let element_type = contract_array_ref_element_type(contract_environment.array_refs, expression)
        .or_else(|| pointer.c_type().pointee_type())
        .ok_or_else(|| "array reference pointer has no modeled element type".to_string())?;
    Ok(ClickArrayRef {
        memory,
        pointer: pointer.into_pointer(),
        element_type,
    })
}

/// A proposition or expression that reads memory the state shows freed is
/// not stated at this state; every other load obligation is certification's
/// to discharge from the path's facts.
fn refuse_impossible_loads(
    obligations: &[Proposition],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    if let Some(obligation) = obligations.iter().find(|obligation| {
        crate::kernel::c_loadability_obligation_impossible_with_assumptions(obligation, assumptions)
    }) {
        // `Debug` on a loadability obligation prints the whole memory
        // snapshot it is indexed by; the bounded sentence names the base and
        // width, which is what the reader has to fix.
        return Err(format!(
            "the proposition reads memory that is not viewable here: {}",
            crate::surface::diagnostics::describe_pure_fact(
                obligation,
                ParameterBinding::default()
            )
        ));
    }
    Ok(())
}

/// The states a fixed-state lowering runs at, with the values in scope at
/// each: the entry state and the current state, each binding the proof's
/// parameter and proof-local values where the state does not bind the name,
/// and `result` bound on the current state.
pub(in crate::surface::proof) struct FixedStateLowering {
    pub(in crate::surface::proof) entry_state: CState,
    pub(in crate::surface::proof) lowering_state: CState,
    pub(in crate::surface::proof) element_types: BTreeMap<String, CType>,
    pub(in crate::surface::proof) entry_values: BTreeMap<String, CValue>,
    pub(in crate::surface::proof) current_values: BTreeMap<String, CValue>,
}

impl FixedStateLowering {
    // Capture only names referenced by the expression or proposition. State
    // handles retain complete memory/resources, while indexed local queries avoid
    // work proportional to unrelated caller bindings.
    fn for_expression(
        expression: &ContractExpression,
        contract_environment: ContractEnvironment<'_>,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
    ) -> Self {
        Self::for_names(
            crate::surface::lowering::contract_expression_referenced_names(expression),
            contract_environment,
            pre_state,
            state,
            result,
            true,
        )
    }

    fn for_proposition(
        proposition: &ClickProposition,
        contract_environment: ContractEnvironment<'_>,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
    ) -> Self {
        let mut names = BTreeSet::new();
        crate::surface::lowering::collect_click_proposition_referenced_names(
            proposition,
            &mut names,
        );
        // The full proposition path installs supplied argument values even
        // over array/aggregate places. Integer capture preserves those places;
        // sharing the name selection must not change either binding policy.
        Self::for_names(names, contract_environment, pre_state, state, result, false)
    }

    fn for_names(
        names: BTreeSet<String>,
        contract_environment: ContractEnvironment<'_>,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
        preserve_place_bindings: bool,
    ) -> Self {
        let mut entry_state = pre_state.clone();
        let mut lowering_state = state.clone();
        let mut element_types = BTreeMap::new();
        let mut entry_values = BTreeMap::new();
        let mut current_values = BTreeMap::new();
        for name in names {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(value) = contract_environment.values.get(&name) {
                if entry_state.locals().get(&name).is_none()
                    && (!preserve_place_bindings || !entry_state.locals().contains_name(&name))
                {
                    entry_state = entry_state.with_local(name.clone(), value.clone());
                }
                if lowering_state.locals().get(&name).is_none()
                    && (!preserve_place_bindings || !lowering_state.locals().contains_name(&name))
                {
                    lowering_state = lowering_state.with_local(name.clone(), value.clone());
                }
            }
            if let Some(element_type) = lowering_state
                .locals()
                .array_object_element_type(&name)
                .or_else(|| {
                    contract_environment
                        .array_refs
                        .get(&name)
                        .map(|array| array.element_type)
                })
            {
                element_types.insert(name.clone(), element_type);
            }
            if let Some(value) = entry_state.locals().get(&name) {
                entry_values.insert(name.clone(), value.clone());
            }
            if let Some(value) = lowering_state.locals().get(&name) {
                current_values.insert(name, value.clone());
            }
        }
        if let Some(result) = result {
            lowering_state =
                lowering_state.with_local(crate::kernel::C_CONTRACT_RESULT_NAME, result.clone());
        }
        Self {
            entry_state,
            lowering_state,
            element_types,
            entry_values,
            current_values,
        }
    }

    pub(in crate::surface::proof) fn new(
        contract_environment: ContractEnvironment<'_>,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
    ) -> Self {
        let bound = |state: &CState| {
            let mut bound = state.clone();
            for (name, value) in contract_environment.values {
                if bound.locals().get(name).is_none() {
                    bound = bound.with_local(name.clone(), value.clone());
                }
            }
            bound
        };
        let entry_state = bound(pre_state);
        let mut lowering_state = bound(state);
        if let Some(result) = result {
            lowering_state =
                lowering_state.with_local(crate::kernel::C_CONTRACT_RESULT_NAME, result.clone());
        }
        let mut element_types = contract_environment
            .array_refs
            .iter()
            .map(|(name, array_ref)| (name.clone(), array_ref.element_type))
            .collect::<BTreeMap<_, _>>();
        element_types.extend(
            lowering_state
                .locals()
                .array_object_values()
                .map(|(name, _, element_type)| (name.to_string(), element_type)),
        );
        let entry_values = entry_state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect();
        let current_values = lowering_state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect();
        Self {
            entry_state,
            lowering_state,
            element_types,
            entry_values,
            current_values,
        }
    }
}

pub(in crate::surface::proof) fn reverse_surface_equality(
    proposition: &ClickProposition,
) -> Option<ClickProposition> {
    if let ClickProposition::At {
        selector,
        proposition,
    } = proposition
    {
        return reverse_surface_equality(proposition).map(|reversed| ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(reversed),
        });
    }
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = proposition
    else {
        return None;
    };
    Some(ClickProposition::Comparison {
        left: right.clone(),
        operator: ComparisonOperator::Equal,
        right: left.clone(),
    })
}

pub(in crate::surface::proof) fn reverse_kernel_equality(
    proposition: Proposition,
) -> Option<Proposition> {
    match proposition {
        Proposition::Equal(left, right) => Some(Proposition::Equal(right, left)),
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(right, left), true),
        ),
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(right, left), true),
        ),
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(right, left), true),
        ),
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::PointerEqual(right, left), true),
        ),
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => Some(
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(right, left), true),
        ),
        _ => None,
    }
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn finish_ordered_proof_units<'a>(
    mut expansion_capture: Option<&mut ExpansionCapture>,
    units: Vec<Proof<'a>>,
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claims: &[FunctionClaimRef<'_>],
    require_explicit_closers: bool,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: &CExecutionEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    // Every theorem the contexts issue shares these two copies. A theorem is
    // issued per path and claim, and each used to carry its own copy of the
    // grouped proof, so finishing cost the proof's size times the number of
    // theorems.
    let shared_function_block = std::sync::Arc::new(function_block.clone());
    let shared_tactics: std::sync::Arc<[ProofTactic]> = std::sync::Arc::from(tactics);
    let mut verified: Vec<VerifiedCTheorem> = Vec::new();
    // The positions of `verified` by claim and by claim and theorem. A
    // theorem already issued by another context equals one filed under its
    // own claim and theorem, so a duplicate is found there instead of by
    // comparing it with every theorem issued so far.
    let mut verified_by_claim: BTreeMap<(bool, usize), Vec<usize>> = BTreeMap::new();
    let mut verified_by_theorem: BTreeMap<(bool, usize, Theorem), Vec<usize>> = BTreeMap::new();
    let mut captured_paths = Vec::new();
    let mut context_count = 0;
    let mut claim_surface_builders: Vec<(VerifiedClaim, Vec<ProofCertificateBuilder>)> = Vec::new();
    for proof in units {
        context_count += 1;
        let view = proof.finalization_view()?;
        let (cursor, proof_site) = (
            &view.execution.presentation.expansion,
            view.context.constants.proof_site.as_ref(),
        );
        let path_choices = cursor.deferred_expansion_path_choices.to_vec();
        resume_deferred_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            cursor,
            proof_site,
        )?;
        let path_had_deferred_capture = cursor.deferred_tactic_capture.is_some();
        let result_before = expansion_capture
            .as_deref()
            .is_some_and(|capture| capture.result.is_some());
        let mut context_surface_builders = Vec::new();
        let theorems = crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &function_block.contract_claim_label(),
            "proof context finishing",
            || {
                finish_ordered_proof(
                    expansion_capture.as_deref_mut(),
                    proof,
                    source_path,
                    &shared_function_block,
                    parsed_function,
                    claims,
                    require_explicit_closers,
                    spec_definitions,
                    resource_environment,
                    theorem_environment,
                    function_environment,
                    function,
                    arguments,
                    &shared_tactics,
                    &mut context_surface_builders,
                )
            },
        )?;
        for (claim, builder) in context_surface_builders {
            match claim_surface_builders
                .iter_mut()
                .find(|(existing, _)| *existing == claim)
            {
                Some((_, builders)) => builders.push(builder),
                None => claim_surface_builders.push((claim, vec![builder])),
            }
        }
        for theorem in theorems {
            let claim_key = verified_claim_key(&theorem.claim);
            let theorem_key = (claim_key.0, claim_key.1, theorem.theorem.clone());
            let issued = verified_by_theorem.entry(theorem_key).or_default();
            if issued.iter().any(|position| verified[*position] == theorem) {
                continue;
            }
            issued.push(verified.len());
            verified_by_claim
                .entry(claim_key)
                .or_default()
                .push(verified.len());
            verified.push(theorem);
        }
        let path_finished_capture = path_had_deferred_capture
            && !result_before
            && expansion_capture
                .as_deref()
                .is_some_and(|capture| capture.result.is_some());
        if path_finished_capture {
            let captured = take_path_tactic_expansion_capture(expansion_capture.as_deref_mut())?;
            captured_paths.push(ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(&captured)
                    .map_err(|error| {
                        ClickError::new(format!(
                            "captured branch expansion was not a simple proof: {error:?}"
                        ))
                    })?
                    .steps()
                    .to_vec(),
                path_choices,
                ..ProofCertificateBuilder::default()
            });
        }
    }
    // A structured proof produced one check context per logical case, and
    // each context's claim-level surface record covers only the execution
    // paths its case owns. Expansion synthesizes their provenance at the
    // recorded branch choices; a per-context record must not survive as the
    // claim's expansion.
    if context_count > 1 {
        crate::instrumentation::measure_operation(
            function_block.signature().name(),
            &function_block.contract_claim_label(),
            "surface context synthesis",
            || {
                for (claim, builders) in claim_surface_builders {
                    // Contexts that recorded branch choices keep their surface `if`
                    // even when every case produced the same steps: check still
                    // needs the case split to cross the branch statement. Contexts
                    // without choices and identical records collapse to one record.
                    let merged = if builders.iter().all(|builder| {
                        builder.path_choices.is_empty() && builder.steps == builders[0].steps
                    }) {
                        builders
                            .first()
                            .and_then(|builder| builder.blocker.clone())
                            .map(Err)
                            .unwrap_or_else(|| Ok(builders[0].steps.clone()))
                    } else {
                        synthesize_surface_alternatives(builders)
                    };
                    // The claim's record is admitted once and shared by each
                    // of its theorems; admitting it per theorem cost the
                    // record's size times the claim's paths.
                    let mut admitted = None;
                    for position in verified_by_claim
                        .get(&verified_claim_key(&claim))
                        .map(Vec::as_slice)
                        .unwrap_or_default()
                    {
                        let theorem = &mut verified[*position];
                        if theorem.claim != claim {
                            continue;
                        }
                        let admitted = admitted.get_or_insert_with(|| match &merged {
                            // A merged record that is not a certificate blocks
                            // this claim's expansion; it never becomes one.
                            Ok(steps) => ProofCertificate::from_steps(steps.clone())
                                .map_err(|error| error.raw_summary().to_string()),
                            Err(message) => Err(format!(
                                "could not merge the claim's surface record across branch contexts: {message}"
                            )),
                        });
                        match admitted {
                            Ok(certificate) => {
                                theorem.expanded_proof = Some(certificate.clone());
                                theorem.expansion_blocker = None;
                            }
                            Err(blocker) => {
                                theorem.expanded_proof = None;
                                theorem.expansion_blocker = Some(blocker.clone());
                            }
                        }
                    }
                }
            },
        );
    }
    if !captured_paths.is_empty() {
        let tactics = if captured_paths
            .iter()
            .all(|path| path.steps == captured_paths[0].steps)
        {
            captured_paths[0].steps.clone()
        } else {
            synthesize_surface_alternatives(captured_paths).map_err(|message| {
                ClickError::new(format!(
                    "could not merge selected deferred tactic across branch contexts: {message}"
                ))
            })?
        };
        let allow_empty = tactics.is_empty();
        finish_tactic_expansion_capture(
            expansion_capture,
            &ProofCertificateBuilder {
                steps: tactics,
                ..ProofCertificateBuilder::default()
            },
            allow_empty,
        );
    }
    Ok(verified)
}

/// A verified claim's kind and clause position: equal claims have equal keys.
fn verified_claim_key(claim: &VerifiedClaim) -> (bool, usize) {
    match claim {
        VerifiedClaim::Ensure { index, .. } => (false, *index),
        VerifiedClaim::ExceptionalEnsure { index, .. } => (true, *index),
    }
}

#[cfg(test)]
mod integer_capture_scaling_tests {
    use super::*;

    #[test]
    fn integer_argument_state_selection_scales_with_referenced_names() {
        let expression = ContractExpression::Binding("used".into());
        for size in [16, 256, 4096] {
            let mut state = CState::new().with_local(
                "used",
                CValue::UInt32(crate::kernel::Bitvector32Term::Constant(7)),
            );
            let mut values = BTreeMap::new();
            for index in 0..size {
                let name = format!("unrelated_{index}");
                let value = CValue::UInt32(crate::kernel::Bitvector32Term::Constant(index));
                values.insert(name.clone(), value.clone());
                state = state.with_local(name, value);
            }
            let (selected, work) = crate::persistent::measure_persistent_work(|| {
                FixedStateLowering::for_expression(
                    &expression,
                    ContractEnvironment::new(&values, &ClickArrayRefs::new()),
                    &state,
                    &state,
                    None,
                )
            });
            assert_eq!(selected.entry_values.len(), 1);
            assert_eq!(selected.current_values.len(), 1);
            assert_eq!(
                selected.current_values["used"],
                CValue::UInt32(crate::kernel::Bitvector32Term::Constant(7))
            );
            assert!(
                work <= 64,
                "{size} unrelated locals caused {work} persistent operations"
            );
        }
    }

    #[test]
    fn proposition_state_selection_scales_with_referenced_names() {
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::At {
                selector: SnapshotSelector::Mark("before".into()),
                expression: Box::new(ContractExpression::Binding("used".into())),
            },
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Old(Box::new(ContractExpression::Binding("used".into()))),
        };
        for size in [16, 64, 256, 1024] {
            let mut state = CState::new().with_local("used", crate::kernel::int32(7));
            let mut values = BTreeMap::new();
            for index in 0..size {
                let name = format!("unrelated_{index}");
                let value = crate::kernel::int32(index);
                values.insert(name.clone(), value.clone());
                state = state.with_local(name, value);
            }
            let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                FixedStateLowering::for_proposition(
                    &proposition,
                    ContractEnvironment::new(&values, &ClickArrayRefs::new()),
                    &state,
                    &state,
                    None,
                )
            });
            assert_eq!(selected.entry_values.len(), 1);
            assert_eq!(selected.current_values.len(), 1);
            assert_eq!(selected.current_values["used"], crate::kernel::int32(7));
            assert!(
                work <= 8,
                "{size} unrelated locals caused {work} selection units"
            );
        }
    }
}
