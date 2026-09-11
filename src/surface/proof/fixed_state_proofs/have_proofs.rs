use super::*;

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn lower_fixed_state_proposition(
    proposition: &ClickProposition,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let assumptions = assumptions_from_propositions(available);
    lower_fixed_state_proposition_with_assumptions(
        proposition,
        &assumptions,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
    )
}

/// Lowers one proposition against a fixed symbolic C state and an already-indexed fact context.
///
/// `Proof` keeps this context persistent and incrementally updated, so a
/// local step does not rebuild it by scanning every unrelated fact. Legacy
/// vector callers continue through `lower_fixed_state_proposition` above.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn lower_fixed_state_proposition_with_assumptions(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
    let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
    lower_fixed_state_proposition_with_values_and_assumptions(
        proposition,
        assumptions,
        values,
        &array_refs,
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
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
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel_with_algebraic_values(
        proposition,
        assumptions,
        values,
        array_refs,
        &BTreeMap::new(),
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with_algebraic_values(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
        proposition,
        assumptions,
        values,
        array_refs,
        algebraic_values,
        &crate::persistent::PersistentMap::default(),
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
        &std::collections::BTreeSet::new(),
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: &std::collections::BTreeSet<String>,
) -> Result<Proposition, String> {
    let mut click_function_calls = BTreeSet::new();
    crate::surface::validation::collect_click_function_calls_in_proposition(
        proposition,
        &mut click_function_calls,
    );
    let symbolic_load_assumptions =
        (!click_function_calls.is_empty()).then(|| assumptions.clone().keep_spec_loads_symbolic());
    let assumptions = symbolic_load_assumptions.as_ref().unwrap_or(assumptions);
    let states = FixedStateLowering::new(values, array_refs, pre_state, state, result);
    let spec = crate::surface::lowering::elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
        proposition,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        algebraic_values.clone(),
        integer_values,
        result,
        recorded_snapshots,
        assumptions,
        predicate_environment,
        click_function_environment,
        opaque_click_functions.clone(),
    )?;
    let (lowered, _, obligations) = crate::kernel::c_lower_spec_proposition_at_state(
        &states.lowering_state,
        &spec,
        Some(&states.entry_state),
        assumptions,
    )?;
    refuse_impossible_loads(&obligations)?;
    Ok(lowered)
}

/// The kernel lowering of a proof-side proposition whose calls named in
/// `opaque_click_functions` stay applications: the proof unfolds them itself.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with_opaque_calls(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: &std::collections::BTreeSet<String>,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
        proposition,
        assumptions,
        values,
        array_refs,
        &BTreeMap::new(),
        &crate::persistent::PersistentMap::default(),
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
        opaque_click_functions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_integer_values(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: &std::collections::BTreeSet<String>,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_algebraic_values(
        proposition,
        assumptions,
        values,
        array_refs,
        &BTreeMap::new(),
        integer_values,
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
        opaque_click_functions,
    )
}

/// The one evaluation of a proof-side expression: elaborated into the
/// kernel's spec form like a contract expression and evaluated by the kernel
/// at the proof's state. Calls named in `opaque_click_functions` stay
/// applications: the proof unfolds them itself.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn evaluate_fixed_state_expression_through_kernel(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: &std::collections::BTreeSet<String>,
) -> Result<CValue, String> {
    let mut click_function_calls = BTreeSet::new();
    crate::surface::validation::collect_click_function_calls(expression, &mut click_function_calls);
    let symbolic_load_assumptions =
        (!click_function_calls.is_empty()).then(|| assumptions.clone().keep_spec_loads_symbolic());
    let assumptions = symbolic_load_assumptions.as_ref().unwrap_or(assumptions);
    let states = FixedStateLowering::new(values, array_refs, pre_state, state, result);
    let spec = crate::surface::lowering::elaborate_fixed_state_expression(
        expression,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        result,
        recorded_snapshots,
        assumptions,
        predicate_environment,
        click_function_environment,
        opaque_click_functions.clone(),
    )?;
    let (value, obligations) = crate::kernel::c_evaluate_spec_expression_at_state(
        &states.lowering_state,
        &spec,
        Some(&states.entry_state),
        assumptions,
    )?;
    refuse_impossible_loads(&obligations)?;
    Ok(value)
}

/// Captures an algebraic expression as the symbolic spec term it denotes at
/// this proof state. The kernel will evaluate the captured term together with
/// the theorem clause that consumes it.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn capture_fixed_state_algebraic_expression(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<SpecAlgebraicExpression, String> {
    let states = FixedStateLowering::new(values, array_refs, pre_state, state, result);
    crate::surface::lowering::elaborate_fixed_state_algebraic_expression(
        expression,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        result,
        recorded_snapshots,
        assumptions,
        predicate_environment,
        click_function_environment,
        BTreeSet::new(),
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn capture_fixed_state_algebraic_value(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    snapshots: &RecordedSnapshots,
    predicates: &PredicateEnvironment,
    functions: &ClickFunctionEnvironment,
) -> Result<crate::kernel::AlgebraicTerm, String> {
    let states = FixedStateLowering::new(values, array_refs, pre_state, state, None);
    let spec = crate::surface::lowering::elaborate_fixed_state_algebraic_expression(
        expression,
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        None,
        snapshots,
        assumptions,
        predicates,
        functions,
        BTreeSet::new(),
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
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    snapshots: &RecordedSnapshots,
    predicates: &PredicateEnvironment,
    functions: &ClickFunctionEnvironment,
) -> Result<crate::kernel::AlgebraicValue, String> {
    let states = FixedStateLowering::new(values, array_refs, pre_state, state, None);
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
                assumptions,
                predicates,
                functions,
                BTreeSet::new(),
            )?;
            let (value, obligations) = crate::kernel::c_evaluate_spec_expression_at_state(
                &states.lowering_state,
                &spec,
                Some(&states.entry_state),
                assumptions,
            )?;
            if obligations.iter().any(|o| !assumptions.proves(o)) {
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
                assumptions,
                predicates,
                functions,
                BTreeSet::new(),
            )?;
            crate::kernel::capture_spec_integer_value(
                &states.lowering_state,
                &spec,
                Some(&states.entry_state),
                assumptions,
            )
            .map(crate::kernel::AlgebraicValue::Integer)
        }
        crate::kernel::ResourceFieldType::Algebraic(_) => {
            let spec = crate::surface::lowering::elaborate_fixed_state_algebraic_expression(
                expression,
                states.element_types,
                &states.entry_state,
                states.entry_values,
                states.current_values,
                None,
                snapshots,
                assumptions,
                predicates,
                functions,
                BTreeSet::new(),
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
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CValue, String> {
    evaluate_c_fragment_with_binding_policy(
        expression,
        assumptions,
        values,
        array_refs,
        state,
        result,
        false,
    )
}

/// Resource clauses use stable logical arguments even after the C parameter
/// changes; static addresses and memory still belong to the exact frontier.
pub(in crate::surface) fn evaluate_resource_fragment_through_kernel(
    expression: &CExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CValue, String> {
    evaluate_c_fragment_with_binding_policy(
        expression,
        assumptions,
        values,
        array_refs,
        state,
        result,
        true,
    )
}

fn evaluate_c_fragment_with_binding_policy(
    expression: &CExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    result: Option<&CValue>,
    logical_arguments: bool,
) -> Result<CValue, String> {
    let mut states = FixedStateLowering::new(values, array_refs, state, state, result);
    if logical_arguments {
        states.entry_values.extend(values.clone());
        states.current_values.extend(values.clone());
    }
    let spec = crate::surface::lowering::elaborate_fixed_state_expression(
        &ContractExpression::CFragment(expression.clone()),
        states.element_types,
        &states.entry_state,
        states.entry_values,
        states.current_values,
        result,
        &RecordedSnapshots::new(),
        assumptions,
        &PredicateEnvironment::new(&[]),
        &ClickFunctionEnvironment::new(&[]),
        std::collections::BTreeSet::new(),
    )?;
    let (value, obligations) = crate::kernel::c_evaluate_spec_expression_at_state(
        &states.lowering_state,
        &spec,
        Some(&states.entry_state),
        assumptions,
    )?;
    refuse_impossible_loads(&obligations)?;
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
            &[],
            &[],
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
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn evaluate_fixed_state_array_ref_through_kernel(
    expression: &ContractExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<ClickArrayRef, String> {
    if let ContractExpression::Binding(name)
    | ContractExpression::CFragment(CExpression::Variable(name))
    | ContractExpression::CBinding(name) = expression
        && let Some(array_ref) = array_refs.get(name)
    {
        return Ok(array_ref.clone());
    }
    let value = evaluate_fixed_state_expression_through_kernel(
        expression,
        assumptions,
        values,
        array_refs,
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
        &std::collections::BTreeSet::new(),
    )?;
    let CValue::Pointer(pointer) = value else {
        return Err(format!(
            "array reference expression did not evaluate to a pointer: `{value:?}`"
        ));
    };
    let memory = match expression {
        ContractExpression::Old(_) => pre_state.memory().clone(),
        ContractExpression::At { selector, .. } => {
            selected_snapshot_state(selector, pre_state, recorded_snapshots)?
                .memory()
                .clone()
        }
        _ => state.memory().clone(),
    };
    Ok(ClickArrayRef {
        memory,
        pointer: pointer.into_pointer(),
        element_type: contract_array_ref_element_type(array_refs, expression)
            .unwrap_or(CType::Int32),
    })
}

/// A proposition or expression that reads memory the state shows freed is
/// not stated at this state; every other load obligation is certification's
/// to discharge from the path's facts.
fn refuse_impossible_loads(obligations: &[Proposition]) -> Result<(), String> {
    if let Some(obligation) = obligations
        .iter()
        .find(|obligation| crate::kernel::c_loadability_obligation_impossible(obligation))
    {
        return Err(format!(
            "the proposition reads memory that is not loadable here: {obligation:?}"
        ));
    }
    Ok(())
}

/// The states a fixed-state lowering runs at, with the values in scope at
/// each: the entry state and the current state, each binding the proof's
/// parameter and proof-local values where the state does not bind the name,
/// and `result` bound on the current state.
struct FixedStateLowering {
    entry_state: CState,
    lowering_state: CState,
    element_types: BTreeMap<String, CType>,
    entry_values: BTreeMap<String, CValue>,
    current_values: BTreeMap<String, CValue>,
}

impl FixedStateLowering {
    fn new(
        values: &BTreeMap<String, CValue>,
        array_refs: &ClickArrayRefs,
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
    ) -> Self {
        let bound = |state: &CState| {
            let mut bound = state.clone();
            for (name, value) in values {
                if bound.locals().get(name).is_none() {
                    bound = bound.with_local(name.clone(), value.clone());
                }
            }
            bound
        };
        let entry_state = bound(pre_state);
        let mut lowering_state = bound(state);
        if let Some(result) = result {
            lowering_state = lowering_state.with_local("result", result.clone());
        }
        let mut element_types = array_refs
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

#[allow(clippy::too_many_arguments)]
fn lower_fixed_state_proposition_with_values_and_assumptions(
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    values: BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    recorded_snapshots: &RecordedSnapshots,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_fixed_state_proposition_through_kernel(
        proposition,
        assumptions,
        &values,
        array_refs,
        pre_state,
        state,
        result,
        recorded_snapshots,
        predicate_environment,
        click_function_environment,
    )
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
pub(in crate::surface::proof) fn plan_smart_have_in_current_state(
    have: &ProofHave,
    claim_label: &str,
    outer_tactic_index: usize,
    available: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    recorded_snapshots: &RecordedSnapshots,
    surface_propositions: &SurfacePropositionMap,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    prelowered_goal: Option<&Proposition>,
) -> Result<(Proposition, SimpEvidence), ClickError> {
    // Plan and check this proof once. Surface expansion must lower this exact
    // plan; it must not search for a different proof if lowering is incomplete.
    // Snapshot transport belongs to the statement transition that changed the
    // memory and reaches a later `have` as an exact current-state assumption.
    let restricted_simp = matches!(
        &have.proof,
        SourceProof::Script(tactics)
            if matches!(tactics.last(), Some(ProofTactic::SimpUsing(_)))
    );
    // Restricted simplification must reason from its named equalities; goal
    // lowering must not silently apply those (or other ambient equalities)
    // before the smart plan is recorded, or expansion loses a required proof
    // step. Keep only the facts needed to write direct program values.
    let _prologue_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: lowering fact preparation",
    );
    let direct_lowering_facts = if restricted_simp {
        facts_for_restricted_simp_lowering(available)
    } else {
        facts_for_smart_have_lowering(available)
    };
    drop(_prologue_span);
    let goal_lowering = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: goal lowering",
    );
    // A caller that already created the checked Proof goal owns its lowering.
    // Planning against a freshly lowered sibling can emit a certificate that
    // checks only against an internal representation and fails after surface
    // expansion re-lowers the goal normally.
    let fact = if let Some(prelowered_goal) = prelowered_goal {
        prelowered_goal.clone()
    } else {
        match lower_fixed_state_proposition(
            &have.proposition,
            &direct_lowering_facts,
            parameters,
            arguments,
            pre_state,
            state,
            None,
            recorded_snapshots,
            predicate_environment,
            click_function_environment,
        ) {
            Ok(fact) => fact,
            Err(message) if restricted_simp => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: could not lower restricted `simp` goal without applying an ambient equality: {message}"
                )));
            }
            Err(message) => match lower_fixed_state_proposition(
                &have.proposition,
                &facts_for_simple_goal_lowering(available),
                parameters,
                arguments,
                pre_state,
                state,
                None,
                recorded_snapshots,
                predicate_environment,
                click_function_environment,
            ) {
                Ok(fact) => fact,
                Err(fallback_message) => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` have proof {outer_tactic_index}: could not lower pure goal: {fallback_message}\n  direct lowering also failed: {message}"
                    )));
                }
            },
        }
    };
    drop(goal_lowering);
    let unfold_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: predicate unfolding",
    );
    let available = if unfolded_predicates.is_empty() {
        available.to_vec()
    } else {
        unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            available,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` have proof {outer_tactic_index}: could not unfold available facts: {message}"
            ))
        })?
    };
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &fact,
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` have proof {outer_tactic_index}: could not unfold pure goal: {message}"
        ))
    })?;
    let restricted_surfaces = match &have.proof {
        SourceProof::Script(tactics) => tactics.last().and_then(|tactic| match tactic {
            ProofTactic::SimpUsing(simp) => Some(&simp.premises),
            _ => None,
        }),
        _ => None,
    };
    let reasoning_available = if let Some(surfaces) = restricted_surfaces {
        // Restricted simplification limits which facts may prove the goal,
        // not which certified bounds may establish that a named premise's
        // memory expressions are defined. Keep scalar/order facts for that
        // lowering step; the `exact` vector below remains the entire
        // simplifier context.
        let lowering_facts = facts_for_restricted_simp_lowering(&available);
        let mut exact = Vec::new();
        for surface in surfaces {
            if let Some(recorded) = surface_propositions.available_kernel(surface, &available) {
                exact.push(recorded.clone());
                continue;
            }
            let lowered = lower_fixed_state_proposition(
                surface,
                &lowering_facts,
                parameters,
                arguments,
                pre_state,
                state,
                None,
                recorded_snapshots,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: could not lower `simp` premise `{}`: {message}",
                    describe_click_proposition(surface)
                ))
            })?;
            let exact_available = available
                .iter()
                .find(|fact| *fact == &lowered || condition_polarity_equivalent(fact, &lowered))
                .cloned()
                .or_else(|| {
                    exact_proper_conjunct_is_available(&lowered, &available)
                        .then_some(lowered.clone())
                })
                .or_else(|| exactly_available_fact(&lowered, &available))
                .or_else(|| {
                    // Load variables are kernel-internal;
                    // recorded equalities chained through one are the same
                    // user-level fact.
                    super::super::fact_reasoning::premise_bridged_by_load_variable_chain(
                        &lowered, &available,
                    )
                    .then_some(lowered.clone())
                });
            let Some(exact_fact) = exact_available else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` have proof {outer_tactic_index}: `simp` listed a premise that is not exactly available\n  Click: {}\n  lowered: {}",
                    describe_click_proposition(surface),
                    describe_pure_fact(&lowered, parameters, arguments),
                )));
            };
            exact.push(exact_fact);
        }
        exact
    } else {
        available.clone()
    };
    drop(unfold_span);
    let context_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: assumption context build",
    );
    let assumptions = assumptions_from_propositions(&reasoning_available);
    drop(context_span);
    let _equivalence_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: exact and equivalent goal checks",
    );
    if reasoning_available.contains(&goal) {
        return Ok((fact, SimpEvidence::Assumption));
    }
    if matches!(normalize_proposition(&goal), SimpProposition::True) {
        return Ok((fact, SimpEvidence::Normalize));
    }
    if quantified_equivalent_available_fact(&goal, &reasoning_available).is_some() {
        return Ok((fact, SimpEvidence::Assumption));
    }
    if let Some(equivalent) = reasoning_available
        .iter()
        .find(|available| **available == goal)
        && let Some(derivation) =
            minimal_proposition_derivation(&goal, std::slice::from_ref(equivalent))?
    {
        return Ok((fact, SimpEvidence::Derivation(derivation)));
    }
    drop(_equivalence_span);
    let condition_search = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: condition premise search",
    );
    let searched = search_condition_derivation(&goal, &reasoning_available)?;
    drop(condition_search);
    if let Some(derivation) = searched {
        return Ok((fact, SimpEvidence::Derivation(derivation)));
    }

    let _simp_span = crate::instrumentation::OperationTiming::new(
        "have",
        claim_label,
        "smart have: simp certificate planning",
    );
    let Some(plan) = plan_simp_certificate(&goal, &assumptions) else {
        let mut message = format!(
            "`{claim_label}` tactic {outer_tactic_index}: `have` failed: {}",
            describe_missing_pure_fact(
                &goal,
                &reasoning_available,
                state.resources().facts(),
                parameters,
                arguments,
                &[],
            )
        );
        if matches!(goal, Proposition::ConditionIs(_, _)) {
            message.push_str("\n  ");
            message.push_str(&describe_condition_search_miss(
                &goal,
                &reasoning_available,
                parameters,
                arguments,
            ));
        }
        return Err(ClickError::new(message));
    };
    if !check_simp_certificate(&goal, &assumptions, &plan) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {outer_tactic_index}: planned smart `have` certificate failed validation"
        )));
    }
    Ok((fact, plan))
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
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: &CExecutionEnvironment,
    function: &CFunction,
    arguments: &[CExpression],
    tactics: &[ProofTactic],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let mut verified = Vec::new();
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
            &format!("{}.contract", function_block.signature().name()),
            "proof context finishing",
            || {
                finish_ordered_proof(
                    expansion_capture.as_deref_mut(),
                    proof,
                    source_path,
                    function_block,
                    parsed_function,
                    claims,
                    require_explicit_closers,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                    theorem_environment,
                    function_environment,
                    function,
                    arguments,
                    tactics,
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
            if !verified.contains(&theorem) {
                verified.push(theorem);
            }
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
            &format!("{}.contract", function_block.signature().name()),
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
                    for theorem in &mut verified {
                        if theorem.claim != claim {
                            continue;
                        }
                        match &merged {
                            Ok(steps) => {
                                theorem.expanded_proof =
                                    Some(ProofCertificate::from_steps(steps.clone()));
                                theorem.expansion_blocker = None;
                            }
                            Err(message) => {
                                theorem.expanded_proof = None;
                                theorem.expansion_blocker = Some(format!(
                                    "could not merge the claim's surface record across branch contexts: {message}"
                                ));
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
