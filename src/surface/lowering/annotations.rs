use super::*;
use crate::kernel::CPredicateUnfolding;

type FunctionContractSummary = (
    Vec<SpecProposition>,
    Vec<SpecProposition>,
    Vec<CMemorySegment>,
    Vec<CFunctionContractClaim>,
    bool,
    Vec<CPredicateUnfolding>,
);

pub(in crate::surface) fn lower_composite_resource_condition(
    definition: &ResourceDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Option<SpecProposition>, ClickError> {
    let Some(condition) = definition
        .composite_body()
        .expect("only composite definitions have conditions")
        .condition()
    else {
        return Ok(None);
    };
    let entry_state = CState::new();
    let mut lowerer = AnnotationLowerer {
        structural_clauses: &[],
        function_effects: &[],
        implicit_contract_mutable_segments: &[],
        predicate_environment,
        click_function_environment,
        entry_state: &entry_state,
        result_type: CType::Int32,
        entry_values: BTreeMap::new(),
        parameter_array_element_types: definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
        branch_join_target: None,
        snapshots: None,
        opaque_click_functions: BTreeSet::new(),
        count_assumptions: None,
    };
    let all_predicates = predicate_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let condition = unfold_click_predicates_in_proposition_with_active(
        predicate_environment,
        &all_predicates,
        condition,
        &mut BTreeSet::new(),
    )
    .map_err(ClickError::new)?;
    lowerer
        .click_proposition_to_spec_proposition(&condition, &SpecElaborationContext::default())
        .map(Some)
        .map_err(ClickError::new)
}

pub(in crate::surface) fn lower_composite_resource_facts(
    definition: &ResourceDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<SpecProposition>, ClickError> {
    let body = definition
        .composite_body()
        .expect("only composite definitions have logical facts");
    let entry_state = CState::new();
    let mut lowerer = AnnotationLowerer {
        structural_clauses: &[],
        function_effects: &[],
        implicit_contract_mutable_segments: &[],
        predicate_environment,
        click_function_environment,
        entry_state: &entry_state,
        result_type: CType::Int32,
        entry_values: BTreeMap::new(),
        parameter_array_element_types: definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
        branch_join_target: None,
        snapshots: None,
        opaque_click_functions: BTreeSet::new(),
        count_assumptions: None,
    };
    let all_predicates = predicate_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let mut facts = Vec::new();
    for fact in body.facts() {
        let unfolded = unfold_click_predicates_in_proposition_with_active(
            predicate_environment,
            &all_predicates,
            fact,
            &mut BTreeSet::new(),
        )
        .map_err(ClickError::new)?;
        // Preserve the named fact as the resource's stable logical identity,
        // and retain its fully unfolded kernel definition as the primitive
        // reasoning authority. Checked proof execution and final contract
        // certification can then agree on the former without asking the
        // kernel to trust an ambient opaque predicate.
        if &unfolded != fact {
            facts.push(
                lowerer
                    .click_proposition_to_spec_proposition(fact, &SpecElaborationContext::default())
                    .map_err(ClickError::new)?,
            );
        }
        facts.push(
            lowerer
                .click_proposition_to_spec_proposition(
                    &unfolded,
                    &SpecElaborationContext::default(),
                )
                .map_err(ClickError::new)?,
        );
    }
    Ok(facts)
}

pub(in crate::surface) fn annotated_function(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    entry_state: &CState,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    inherit_function_effects_into_loops: bool,
) -> Result<CFunction, ClickError> {
    let (resource_requires, resource_ensures) =
        function_resource_summary(function_block, parsed_function, resource_environment)?;
    let resource_constructors = function_resource_constructors(function_block)?;
    let (
        contract_requires,
        contract_ensures,
        contract_mutable,
        contract_claims,
        opaque_contract_supported,
        predicate_unfoldings,
    ) = function_contract_summary(
        function_block,
        parsed_function,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    // `consumes` grants the callee a write-capable owned range even when the
    // source has no explicit function-level `mutable` clause. Carry that
    // frame into loop summaries so checked proof artifacts retain the same
    // memory-effect evidence as independent contract certification.
    let implicit_contract_mutable_segments = if function_block.effects().is_empty() {
        contract_mutable.as_slice()
    } else {
        &[]
    };
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        function_effects: if inherit_function_effects_into_loops {
            function_block.effects()
        } else {
            &[]
        },
        implicit_contract_mutable_segments,
        predicate_environment,
        click_function_environment,
        entry_state,
        result_type: if parsed_function.return_struct_name().is_some() {
            CType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        entry_values: parameter_values(parsed_function.parameters(), arguments)?,
        parameter_array_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                if parameter.is_struct_value() {
                    return Some((parameter.name().to_string(), CType::Int32));
                }
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_000_000,
        branch_join_target: None,
        snapshots: None,
        opaque_click_functions: BTreeSet::new(),
        count_assumptions: None,
    };
    let body = lowerer.lower_statement(parsed_function.body())?;
    let source_body = parsed_function.to_kernel_function().body().clone();
    let mut function = c_function(
        if parsed_function.return_struct_name().is_some() {
            CType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        parsed_function.name().to_string(),
        parsed_function
            .parameters()
            .iter()
            .map(syntax::C0Parameter::to_kernel_parameter)
            .collect(),
        body,
    )
    .with_source_body(source_body);
    if let Some(struct_name) = parsed_function.return_struct_name() {
        let layout = parsed_function
            .structs()
            .get(struct_name)
            .expect("struct return has a parsed layout")
            .to_kernel_aggregate_layout();
        function = function.with_return_aggregate_layout(layout);
    }
    let function = function
        .with_global_variables(
            parsed_function
                .globals()
                .values()
                .filter_map(syntax::C0Global::to_kernel_global)
                .collect(),
        )
        .with_global_arrays(
            parsed_function
                .global_arrays()
                .values()
                .filter_map(syntax::C0GlobalArray::to_kernel_global_array)
                .collect(),
        )
        .with_static_variables(
            parsed_function
                .static_locals()
                .values()
                .filter_map(syntax::C0StaticLocal::to_kernel_static)
                .collect(),
        )
        .with_string_literals(
            parsed_function
                .string_literals()
                .iter()
                .map(|literal| {
                    crate::kernel::CStringLiteral::new(
                        literal.name().to_string(),
                        literal.bytes().to_vec(),
                    )
                })
                .collect(),
        )
        .with_resource_summary(resource_requires, resource_ensures)
        .with_resource_constructors(resource_constructors)
        .with_composite_resource_definitions(composite_resource_definitions(
            resource_environment,
            predicate_environment,
            click_function_environment,
        )?)
        .with_predicate_unfoldings(predicate_unfoldings)
        .with_contract(
            contract_requires,
            contract_ensures,
            contract_mutable,
            contract_claims,
            opaque_contract_supported,
        );
    Ok(if function_block.effects().is_empty() {
        function.with_resource_derived_mutable_frame()
    } else {
        function
    })
}

/// Lowers one `branch ensuring` fact as a state-parametric kernel
/// proposition. Unlike fixed-state proof lowering, this keeps C bindings as
/// expressions so the kernel can check the same interface against both
/// concrete arm states and the abstract successor state.
pub(in crate::surface) fn lower_branch_interface_fact(
    proposition: &ClickProposition,
    parsed_function: &syntax::C0Function,
    entry_state: &CState,
    branch_join_target: &ProgramPointRef,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<SpecProposition, ClickError> {
    let mut lowerer = AnnotationLowerer {
        structural_clauses: &[],
        function_effects: &[],
        implicit_contract_mutable_segments: &[],
        predicate_environment,
        click_function_environment,
        entry_state,
        result_type: if parsed_function.return_struct_name().is_some() {
            CType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        entry_values: parameter_values(parsed_function.parameters(), arguments)?,
        parameter_array_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_300_000,
        branch_join_target: Some(branch_join_target),
        snapshots: None,
        opaque_click_functions: BTreeSet::new(),
        count_assumptions: None,
    };
    lowerer
        .click_proposition_to_spec_proposition(proposition, &SpecElaborationContext::default())
        .map_err(ClickError::new)
}

/// The elaborator and context of a fixed-state proof: `old(...)` names the
/// function entry, a predicate call stays a predicate, recorded snapshots
/// are fixed states, and the proof's current locals and `result` are fixed
/// values. `array_element_types` names the array parameters and proof-local
/// array bindings in scope; `opaque_click_functions` names the calls the
/// proof unfolds itself.
#[allow(clippy::too_many_arguments)]
fn fixed_state_elaboration<'a>(
    array_element_types: BTreeMap<String, CType>,
    entry_state: &'a CState,
    entry_values: BTreeMap<String, CValue>,
    current_values: BTreeMap<String, CValue>,
    result: Option<&CValue>,
    snapshots: &'a RecordedSnapshots,
    assumptions: &'a PureFactContext,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    opaque_click_functions: BTreeSet<String>,
) -> (AnnotationLowerer<'a>, SpecElaborationContext) {
    let lowerer = AnnotationLowerer {
        structural_clauses: &[],
        function_effects: &[],
        predicate_environment,
        click_function_environment,
        entry_state,
        result_type: result.map(CValue::c_type).unwrap_or(CType::Int32),
        entry_values,
        parameter_array_element_types: array_element_types,
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 2_000_000,
        branch_join_target: None,
        implicit_contract_mutable_segments: &[],
        snapshots: Some(snapshots),
        opaque_click_functions,
        count_assumptions: Some(assumptions),
    };
    // The proof's current locals are fixed values in every context: a name a
    // snapshot or the entry does not bind keeps its current value, as the
    // proof reads it.
    let mut context = SpecElaborationContext::default();
    context.values = current_values
        .into_iter()
        .map(|(name, value)| (name, SpecExpression::Value(value)))
        .collect();
    if let Some(result) = result {
        context
            .values
            .insert("result".to_string(), SpecExpression::Value(result.clone()));
    }
    (lowerer, context)
}

/// Elaborates a proposition stated in a fixed-state proof into the kernel's
/// spec form, exactly as a contract clause is elaborated; the kernel then
/// lowers the result at the proof's state.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_proposition(
    proposition: &ClickProposition,
    array_element_types: BTreeMap<String, CType>,
    entry_state: &CState,
    entry_values: BTreeMap<String, CValue>,
    current_values: BTreeMap<String, CValue>,
    result: Option<&CValue>,
    snapshots: &RecordedSnapshots,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: BTreeSet<String>,
) -> Result<SpecProposition, String> {
    let (mut lowerer, context) = fixed_state_elaboration(
        array_element_types,
        entry_state,
        entry_values,
        current_values,
        result,
        snapshots,
        assumptions,
        predicate_environment,
        click_function_environment,
        opaque_click_functions,
    );
    lowerer.click_proposition_to_spec_proposition(proposition, &context)
}

/// Elaborates an expression stated in a fixed-state proof into the kernel's
/// spec form, as `elaborate_fixed_state_proposition` does a proposition; the
/// kernel then evaluates the result at the proof's state.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_expression(
    expression: &ContractExpression,
    array_element_types: BTreeMap<String, CType>,
    entry_state: &CState,
    entry_values: BTreeMap<String, CValue>,
    current_values: BTreeMap<String, CValue>,
    result: Option<&CValue>,
    snapshots: &RecordedSnapshots,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: BTreeSet<String>,
) -> Result<SpecExpression, String> {
    let (mut lowerer, context) = fixed_state_elaboration(
        array_element_types,
        entry_state,
        entry_values,
        current_values,
        result,
        snapshots,
        assumptions,
        predicate_environment,
        click_function_environment,
        opaque_click_functions,
    );
    lowerer.lower_contract_expression_to_spec(expression, &context)
}

/// The pure function definitions in spec form, for the kernel to evaluate
/// constant applications by. Every call in a body stays an application; the
/// kernel unfolds those it can. A definition the elaboration cannot express
/// is left out, and its applications stay opaque.
pub(in crate::surface) fn elaborate_pure_function_definitions(
    click_function_environment: &ClickFunctionEnvironment,
) -> BTreeMap<String, crate::kernel::SpecPureFunctionDefinition> {
    let predicate_environment = PredicateEnvironment::new(&[]);
    let entry_state = CState::new();
    let opaque_click_functions = click_function_environment
        .definitions
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut definitions = BTreeMap::new();
    for (name, definition) in &click_function_environment.definitions {
        let mut array_element_types = BTreeMap::new();
        let mut context = SpecElaborationContext::default();
        for parameter in definition.parameters() {
            let variable =
                SpecExpression::CExpression(CExpression::Variable(parameter.name().to_string()));
            context
                .values
                .insert(parameter.name().to_string(), variable.clone());
            if let Some(element_type) = click_array_element_type(parameter.c_type()) {
                array_element_types.insert(parameter.name().to_string(), element_type);
                context.array_refs.insert(
                    parameter.name().to_string(),
                    SpecArrayRef {
                        memory: SpecMemory::Current,
                        pointer: variable,
                        element_type,
                    },
                );
            }
        }
        let mut lowerer = AnnotationLowerer {
            structural_clauses: &[],
            function_effects: &[],
            predicate_environment: &predicate_environment,
            click_function_environment,
            entry_state: &entry_state,
            result_type: CType::Int32,
            entry_values: BTreeMap::new(),
            parameter_array_element_types: array_element_types,
            quantified_values: BTreeMap::new(),
            active_click_functions: BTreeSet::new(),
            loop_index: 0,
            statement_index: 0,
            next_quantifier_variable: 2_000_000,
            branch_join_target: None,
            implicit_contract_mutable_segments: &[],
            snapshots: None,
            opaque_click_functions: opaque_click_functions.clone(),
            count_assumptions: None,
        };
        if let Ok(body) = lowerer.lower_contract_expression_to_spec(definition.body(), &context) {
            definitions.insert(
                name.clone(),
                crate::kernel::SpecPureFunctionDefinition {
                    parameters: definition
                        .parameters()
                        .iter()
                        .map(|parameter| parameter.name().to_string())
                        .collect(),
                    body,
                },
            );
        }
    }
    definitions
}

/// Elaborates one `requires` proposition into the kernel's spec form, exactly
/// as `function_contract_summary` elaborates the contract's clauses; the
/// kernel then lowers it at the function's entry state. A predicate call
/// stays a predicate.
pub(in crate::surface) fn elaborate_requirement_proposition(
    parameters: &[syntax::C0Parameter],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<SpecProposition, String> {
    let entry_state = CState::new();
    let mut lowerer = AnnotationLowerer {
        structural_clauses: &[],
        function_effects: &[],
        implicit_contract_mutable_segments: &[],
        predicate_environment,
        click_function_environment,
        entry_state: &entry_state,
        result_type: CType::Int32,
        entry_values: BTreeMap::new(),
        parameter_array_element_types: parameters
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
        branch_join_target: None,
        snapshots: None,
        opaque_click_functions: BTreeSet::new(),
        count_assumptions: None,
    };
    lowerer.click_proposition_to_spec_proposition(
        proposition,
        &SpecElaborationContext::for_function_contract(),
    )
}

pub(in crate::surface) fn function_contract_summary(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<FunctionContractSummary, ClickError> {
    let entry_state = crate::kernel::initialize_c_function_globals(
        &CState::new(),
        &parsed_function.to_kernel_function(),
    );
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        function_effects: &[],
        implicit_contract_mutable_segments: &[],
        predicate_environment,
        click_function_environment,
        entry_state: &entry_state,
        result_type: parsed_function.return_type().to_kernel_type(),
        entry_values: BTreeMap::new(),
        parameter_array_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        active_click_functions: BTreeSet::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
        branch_join_target: None,
        snapshots: None,
        opaque_click_functions: BTreeSet::new(),
        count_assumptions: None,
    };
    let context = SpecElaborationContext::for_function_contract();
    let all_predicates = predicate_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let unfold_contract_predicates = |proposition: &ClickProposition| {
        unfold_click_predicates_in_proposition_with_active(
            predicate_environment,
            &all_predicates,
            proposition,
            &mut BTreeSet::new(),
        )
    };
    let mut opaque_contract_supported = true;
    let mut predicate_unfoldings = Vec::new();
    let mut requires = Vec::new();
    for proposition in requirement_definedness_surfaces(function_block.requires()) {
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => requires.push(proposition),
            Err(_) => opaque_contract_supported = false,
        }
    }
    for requirement in function_block.requires() {
        let proposition = match requirement.inner() {
            Requirement::Proposition(proposition) => proposition.clone(),
            Requirement::LoadableSegment { segment } => ClickProposition::Loadable {
                segment: segment.clone(),
            },
            Requirement::Resource(_) | Requirement::Labeled { .. } => continue,
        };
        let opaque_predicate = matches!(proposition, ClickProposition::PredicateCall { .. })
            .then(|| lowerer.click_proposition_to_spec_proposition(&proposition, &context))
            .transpose();
        let Ok(proposition) = unfold_contract_predicates(&proposition) else {
            opaque_contract_supported = false;
            continue;
        };
        if !proposition_supported_in_opaque_contract(&proposition) {
            opaque_contract_supported = false;
            continue;
        }
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => {
                if let Ok(Some(predicate)) = opaque_predicate {
                    predicate_unfoldings
                        .push(CPredicateUnfolding::new(predicate, proposition.clone()));
                }
                requires.push(proposition)
            }
            Err(_) => opaque_contract_supported = false,
        }
    }
    let mut ensures = Vec::new();
    for proposition in function_block
        .ensures()
        .iter()
        .filter_map(|clause| match clause.ensure() {
            Ensure::Proposition(proposition) => Some(proposition),
            Ensure::Resource(_) => None,
        })
    {
        let opaque_predicate = matches!(proposition, ClickProposition::PredicateCall { .. })
            .then(|| lowerer.click_proposition_to_spec_proposition(proposition, &context))
            .transpose();
        let Ok(proposition) = unfold_contract_predicates(proposition) else {
            opaque_contract_supported = false;
            continue;
        };
        if !proposition_supported_in_opaque_contract(&proposition) {
            opaque_contract_supported = false;
            continue;
        }
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => {
                if let Ok(Some(predicate)) = opaque_predicate {
                    predicate_unfoldings
                        .push(CPredicateUnfolding::new(predicate, proposition.clone()));
                }
                ensures.push(proposition)
            }
            Err(_) => opaque_contract_supported = false,
        }
    }

    let mut mutable = Vec::new();
    if function_block.effects().is_empty() {
        for requirement in function_block.requires() {
            if let Requirement::Resource(resource) = requirement.inner() {
                collect_owned_resource_memory_segments(
                    resource,
                    resource_environment,
                    parsed_function.parameters(),
                    &mut lowerer,
                    &mut mutable,
                )?;
            }
        }
    }
    for effect in function_block.effects() {
        match effect.effect() {
            Effect::Immutable => {}
            Effect::Mutable(segments) => {
                mutable.extend(segments.iter().map(|segment| {
                    CMemorySegment::new(
                        segment.base.clone(),
                        segment.start.clone(),
                        segment.end.clone(),
                    )
                    .with_element_width(contract_segment_element_width(
                        parsed_function.parameters(),
                        segment,
                    ))
                }));
            }
        }
    }
    let claims = if function_block.effects().is_empty() && function_block.ensures().is_empty() {
        vec![CFunctionContractClaim::body_safety()]
    } else {
        let mut proposition_index = 0;
        let mut resource_index = 0;
        let mut claims = function_block
            .effects()
            .iter()
            .enumerate()
            .map(|(index, _)| CFunctionContractClaim::effect(index))
            .collect::<Vec<_>>();
        for (source_index, ensure) in function_block.ensures().iter().enumerate() {
            claims.push(match ensure.ensure() {
                Ensure::Proposition(_) => {
                    let claim =
                        CFunctionContractClaim::ensure_proposition(source_index, proposition_index);
                    proposition_index += 1;
                    claim
                }
                Ensure::Resource(_) => {
                    let claim =
                        CFunctionContractClaim::ensure_resource(source_index, resource_index);
                    resource_index += 1;
                    claim
                }
            });
        }
        claims
    };
    Ok((
        requires,
        ensures,
        mutable,
        claims,
        opaque_contract_supported,
        predicate_unfoldings,
    ))
}

fn proposition_supported_in_opaque_contract(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => true,
        ClickProposition::At { .. } => false,
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_supported_in_opaque_contract(left)
                && proposition_supported_in_opaque_contract(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. }
        | ClickProposition::RangeAll { body, .. }
        | ClickProposition::RangeAny { body, .. } => proposition_supported_in_opaque_contract(body),
        ClickProposition::Comparison { .. } | ClickProposition::PredicateCall { .. } => true,
    }
}

fn collect_owned_resource_memory_segments(
    resource: &ResourceClause,
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    lowerer: &mut AnnotationLowerer<'_>,
    output: &mut Vec<CMemorySegment>,
) -> Result<(), ClickError> {
    collect_owned_resource_memory_segments_inner(
        resource,
        resource_environment,
        parameters,
        lowerer,
        output,
        &mut BTreeSet::new(),
        None,
    )
}

fn collect_owned_resource_memory_segments_inner(
    resource: &ResourceClause,
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    lowerer: &mut AnnotationLowerer<'_>,
    output: &mut Vec<CMemorySegment>,
    active_resources: &mut BTreeSet<String>,
    active_guard: Option<ClickProposition>,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Quantified { resource, .. } => {
            collect_owned_resource_memory_segments_inner(
                resource,
                resource_environment,
                parameters,
                lowerer,
                output,
                active_resources,
                active_guard,
            )
        }
        ResourceClause::ViewMemory(_) => Ok(()),
        ResourceClause::OwnMemory(segment) => {
            let element_width = contract_segment_element_width(parameters, segment);
            let mut segment = CMemorySegment::new(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
            )
            .with_element_width(element_width);
            if let Some(guard) = active_guard {
                segment = segment.with_guard(
                    lowerer
                        .click_proposition_to_spec_proposition(
                            &guard,
                            &SpecElaborationContext::for_function_contract(),
                        )
                        .map_err(ClickError::new)?,
                );
            }
            output.push(segment);
            Ok(())
        }
        ResourceClause::MemoryAggregate { access, segments } => {
            if *access == ResourceAccessMode::View {
                return Ok(());
            }
            for segment in segments {
                collect_owned_resource_memory_segments_inner(
                    &ResourceClause::OwnMemory(segment.clone()),
                    resource_environment,
                    parameters,
                    lowerer,
                    output,
                    active_resources,
                    active_guard.clone(),
                )?;
            }
            Ok(())
        }
        ResourceClause::Declared {
            access: ResourceAccessMode::View,
            ..
        } => Ok(()),
        ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Token,
            ..
        } => Ok(()),
        ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Composite,
            name,
            arguments,
            ..
        } => {
            if !active_resources.insert(name.clone()) {
                return Ok(());
            }
            let result = (|| {
                let definition = resource_environment.get(name).ok_or_else(|| {
                    ClickError::new(format!("unknown composite resource `{name}`"))
                })?;
                let Some(body) = definition.composite_body() else {
                    return Ok(());
                };
                let substitutions =
                    resource_argument_contract_substitutions(definition, arguments)?;
                let nested_guard = body
                    .condition()
                    .map(|condition| substitute_click_proposition(condition, &substitutions))
                    .transpose()
                    .map_err(ClickError::new)?;
                let active_guard = match (active_guard.clone(), nested_guard) {
                    (Some(outer), Some(inner)) => {
                        Some(ClickProposition::And(Box::new(outer), Box::new(inner)))
                    }
                    (Some(guard), None) | (None, Some(guard)) => Some(guard),
                    (None, None) => None,
                };
                for contained in body.contains() {
                    let contained =
                        substitute_resource_clause_for_summary(contained, &substitutions)
                            .map_err(ClickError::new)?;
                    collect_owned_resource_memory_segments_inner(
                        &contained,
                        resource_environment,
                        parameters,
                        lowerer,
                        output,
                        active_resources,
                        active_guard.clone(),
                    )?;
                }
                Ok(())
            })();
            active_resources.remove(name);
            result
        }
    }
}

struct AnnotationLowerer<'a> {
    structural_clauses: &'a [StructuralClause],
    function_effects: &'a [EffectClause],
    implicit_contract_mutable_segments: &'a [CMemorySegment],
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    entry_state: &'a CState,
    result_type: CType,
    entry_values: BTreeMap<String, CValue>,
    parameter_array_element_types: BTreeMap<String, CType>,
    quantified_values: BTreeMap<String, CValue>,
    active_click_functions: BTreeSet<String>,
    loop_index: usize,
    statement_index: usize,
    next_quantifier_variable: u64,
    branch_join_target: Option<&'a ProgramPointRef>,
    /// The states a proof recorded at program points and marks, when the
    /// proposition is stated inside a proof.
    snapshots: Option<&'a RecordedSnapshots>,
    /// The proof's fact context, under which a count at a recorded state
    /// selects its populations.
    count_assumptions: Option<&'a PureFactContext>,
    /// Calls a proof unfolds itself; they stay applications.
    opaque_click_functions: BTreeSet<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResolvedProgramPoint {
    Current,
    FunctionEntry,
    LoopEntry(usize),
}

impl AnnotationLowerer<'_> {
    fn lower_statement(
        &mut self,
        statement: &syntax::C0Statement,
    ) -> Result<CStatement, ClickError> {
        Ok(match statement {
            syntax::C0Statement::Seq(first, second) => {
                c_seq(self.lower_statement(first)?, self.lower_statement(second)?)
            }
            syntax::C0Statement::While { condition, body }
            | syntax::C0Statement::DoWhile { condition, body } => {
                self.next_statement_index();
                let loop_index = self.next_loop_index();
                let lowered_body = self.lower_statement(body)?;
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_effect_checks(loop_index, body)?;
                if matches!(statement, syntax::C0Statement::DoWhile { .. }) {
                    c_do_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                } else {
                    c_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                }
            }
            syntax::C0Statement::For {
                initializer,
                condition,
                step,
                body,
            } => {
                let lowered_initializer = self.lower_statement(initializer)?;
                self.next_statement_index();
                let loop_index = self.next_loop_index();
                let lowered_body = self.lower_statement(body)?;
                let lowered_step = self.lower_statement(step)?;
                let effect_body = syntax::C0Statement::Seq(body.clone(), step.clone());
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_effect_checks(loop_index, &effect_body)?;
                c_seq(
                    lowered_initializer,
                    c_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        crate::kernel::c_for_body_with_step(lowered_body, lowered_step),
                    ),
                )
            }
            syntax::C0Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.next_statement_index();
                c_if(
                    condition.to_kernel_expression(),
                    self.lower_statement(then_branch)?,
                    self.lower_statement(else_branch)?,
                )
            }
            statement => {
                self.next_statement_index();
                statement.to_kernel_statement()
            }
        })
    }

    fn next_statement_index(&mut self) -> usize {
        let index = self.statement_index;
        self.statement_index += 1;
        index
    }

    fn next_loop_index(&mut self) -> usize {
        let index = self.loop_index;
        self.loop_index += 1;
        index
    }

    fn loop_invariant_checks(
        &mut self,
        loop_index: usize,
    ) -> Result<Vec<CLoopInvariantCheck>, ClickError> {
        let unfolded_predicates = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(|clause| {
                clause
                    .initialize_proof()
                    .into_iter()
                    .chain(clause.preserve_proof())
            })
            .flat_map(SourceProof::unfold_tactic_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        self.structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .enumerate()
            .map(|(item_index, item)| {
                let proposition = unfold_structural_invariant_proposition(
                    self.predicate_environment,
                    item.proposition()
                        .expect("invariant structural item should contain a proposition"),
                    &unfolded_predicates,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "loop {loop_index} invariant {item_index}: {message}"
                    ))
                })?;
                Ok(CLoopInvariantCheck::new(
                    self.click_proposition_to_spec_proposition(
                        &proposition,
                        &SpecElaborationContext::for_loop_invariant(loop_index),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "loop {loop_index} invariant {item_index}: {message}"
                        ))
                    })?,
                    Some(format!("loop {loop_index} invariant {item_index} entry")),
                    Some(format!(
                        "loop {loop_index} invariant {item_index} preservation"
                    )),
                ))
            })
            .collect()
    }

    fn click_proposition_to_spec_proposition(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => Ok(SpecProposition::Comparison {
                left: self.lower_contract_expression_to_spec(left, environment)?,
                operator: c_comparison_operator(*operator),
                right: self.lower_contract_expression_to_spec(right, environment)?,
            }),
            ClickProposition::Separate { left, right } => Ok(SpecProposition::ResourceSeparate {
                left: self.lower_resource_subject_to_spec(left, environment)?,
                right: self.lower_resource_subject_to_spec(right, environment)?,
            }),
            ClickProposition::Contains { parent, child } => Ok(SpecProposition::ResourceContains {
                parent: self.lower_resource_subject_to_spec(parent, environment)?,
                child: self.lower_resource_subject_to_spec(child, environment)?,
            }),
            ClickProposition::Loadable { segment } => {
                let segment_environment = self.spec_segment_environment(segment, environment)?;
                Ok(SpecProposition::MemoryLoadable {
                    memory: segment_environment.current_memory.clone(),
                    base: self
                        .lower_contract_segment_base_to_spec(&segment.base, &segment_environment)?,
                    start: self.lower_c_fragment_to_spec(&segment.start, &segment_environment)?,
                    end: self.lower_c_fragment_to_spec(&segment.end, &segment_environment)?,
                    element_width: self
                        .contract_segment_element_width(segment, &segment_environment),
                })
            }
            ClickProposition::Defined { expression } => Ok(SpecProposition::Defined(
                self.lower_contract_expression_to_spec(expression, environment)?,
            )),
            ClickProposition::At {
                selector,
                proposition,
            } => {
                if let Some(snapshot) = self.snapshot_environment(selector, environment) {
                    return self.click_proposition_to_spec_proposition(proposition, &snapshot);
                }
                match self.resolve_visit_selector(selector)? {
                    ResolvedProgramPoint::Current => {
                        self.click_proposition_to_spec_proposition(proposition, environment)
                    }
                    ResolvedProgramPoint::FunctionEntry => {
                        let old_environment =
                            environment.old_state(&self.entry_values, self.entry_state.memory())?;
                        self.click_proposition_to_spec_proposition(proposition, &old_environment)
                    }
                    _ => Err("`at(...)` propositions are proof-script snapshots".to_string()),
                }
            }
            ClickProposition::And(left, right) => Ok(SpecProposition::And(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::Or(left, right) => Ok(SpecProposition::Or(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::Not(body) => Ok(SpecProposition::Not(Box::new(
                self.click_proposition_to_spec_proposition(body, environment)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(SpecProposition::Implies(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let c_type = c_type.to_kernel_type();
                let value = match c_type {
                    CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
                    c_type if c_type.is_pointer() => {
                        if matches!(c_type, CType::FunctionPointer(_)) {
                            CValue::typed_pointer(Pointer::symbolic_function(variable), c_type)
                        } else {
                            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
                        }
                    }
                    _ => return Err("only int32 and pointer binders are supported".to_string()),
                };
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(name.clone(), SpecExpression::Value(value.clone()));
                let previous = self.quantified_values.insert(name.clone(), value);
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                if c_type == CType::Int32 {
                    Ok(SpecProposition::ForAllInt32 {
                        name: name.clone(),
                        variable,
                        body: Box::new(body),
                    })
                } else {
                    Ok(SpecProposition::ForAllPointer {
                        name: name.clone(),
                        variable,
                        c_type,
                        body: Box::new(body),
                    })
                }
            }
            ClickProposition::Exists { c_type, name, body } => {
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let c_type = c_type.to_kernel_type();
                let value = match c_type {
                    CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
                    c_type if c_type.is_pointer() => {
                        if matches!(c_type, CType::FunctionPointer(_)) {
                            CValue::typed_pointer(Pointer::symbolic_function(variable), c_type)
                        } else {
                            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
                        }
                    }
                    _ => return Err("only int32 and pointer binders are supported".to_string()),
                };
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(name.clone(), SpecExpression::Value(value.clone()));
                let previous = self.quantified_values.insert(name.clone(), value);
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                if c_type == CType::Int32 {
                    Ok(SpecProposition::ExistsInt32 {
                        name: name.clone(),
                        variable,
                        body: Box::new(body),
                    })
                } else {
                    Ok(SpecProposition::ExistsPointer {
                        name: name.clone(),
                        variable,
                        c_type,
                        body: Box::new(body),
                    })
                }
            }
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => {
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let item_value =
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(
                    item.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(item.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(item);
                    }
                }
                let range = spec_range_membership_proposition(start, item_value, end);
                Ok(SpecProposition::ForAllInt32 {
                    name: item.clone(),
                    variable,
                    body: Box::new(SpecProposition::Implies(Box::new(range), Box::new(body))),
                })
            }
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => {
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let item_value =
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(
                    item.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(item.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(item);
                    }
                }
                let range = spec_range_membership_proposition(start, item_value, end);
                Ok(SpecProposition::ExistsInt32 {
                    name: item.clone(),
                    variable,
                    body: Box::new(SpecProposition::And(Box::new(range), Box::new(body))),
                })
            }
            ClickProposition::PredicateCall { name, arguments } => {
                let definition = self
                    .predicate_environment
                    .get(name)
                    .ok_or_else(|| format!("unknown predicate `{name}`"))?;
                let mut lowered_arguments = Vec::new();
                for (parameter, argument) in definition.parameters().iter().zip(arguments) {
                    if parameter_is_click_array_ref(parameter) {
                        let expected_element_type = click_array_element_type(parameter.c_type())
                            .ok_or_else(|| {
                                format!(
                                    "predicate `{}` parameter `{}` is not an array-ref parameter",
                                    definition.name(),
                                    parameter.name()
                                )
                            })?;
                        let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                        if array_ref.element_type != expected_element_type {
                            return Err(format!(
                                "predicate `{}` parameter `{}` expects {:?} array elements, got {:?}",
                                definition.name(),
                                parameter.name(),
                                expected_element_type,
                                array_ref.element_type
                            ));
                        }
                        lowered_arguments.push(SpecPredicateArgument::ArrayRef {
                            memory: array_ref.memory,
                            pointer: array_ref.pointer,
                        });
                    } else {
                        lowered_arguments.push(SpecPredicateArgument::Value(
                            self.lower_contract_expression_to_spec(argument, environment)?,
                        ));
                    }
                }
                Ok(SpecProposition::Predicate {
                    name: name.clone(),
                    arguments: lowered_arguments,
                })
            }
        }
    }

    fn lower_contract_expression_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            ContractExpression::CFragment(expression)
            | ContractExpression::Field {
                lowered: expression,
                ..
            } => self.lower_c_fragment_to_spec(expression, environment),
            ContractExpression::CBinding(name) => {
                self.lower_c_fragment_to_spec(&CExpression::Variable(name.clone()), environment)
            }
            ContractExpression::ResourceCount(resource) => {
                let ResourceClause::Declared {
                    name, arguments, ..
                } = resource.as_ref()
                else {
                    return Err("`count(...)` expects a declared resource".to_string());
                };
                let arguments = arguments
                    .iter()
                    .map(|argument| match argument {
                        ContractExpression::ResourceWildcard => Ok(None),
                        argument => self
                            .lower_contract_expression_to_spec(argument, environment)
                            .map(Some),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                // A count at a recorded state is that state's population.
                if let Some(state) = &environment.snapshot_state {
                    let values = arguments
                        .iter()
                        .map(|argument| match argument {
                            None => Some(None),
                            Some(SpecExpression::Value(value)) => Some(Some(value.clone())),
                            Some(_) => None,
                        })
                        .collect::<Option<Vec<_>>>()
                        .ok_or_else(|| {
                            format!("`count({name})` at a recorded state needs fixed arguments")
                        })?;
                    let assumptions = self.count_assumptions.cloned().unwrap_or_default();
                    return Ok(SpecExpression::Value(CValue::Int32(
                        state.counted_population_sum(name, &values, &assumptions),
                    )));
                }
                let count = SpecExpression::CountedResourceCount {
                    name: name.clone(),
                    arguments,
                };
                // A count named at the function entry is the entry's
                // population, which the kernel evaluates at the entry state.
                Ok(if environment.at_function_entry {
                    SpecExpression::LoopEntrySnapshot(Box::new(count))
                } else {
                    count
                })
            }
            ContractExpression::ResourceWildcard => {
                Err("`_` is only valid inside a `count(...)` resource pattern".to_string())
            }
            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_expression_to_spec(selector, expression, environment),
            // Arithmetic on a pointer offsets it by whole elements, as C does.
            ContractExpression::Add(left, right) => {
                if let Some(element_type) = self.contract_pointer_element_type(left, environment) {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_contract_expression_to_spec(left, environment)?,
                        ),
                        elements: Box::new(
                            self.lower_contract_expression_to_spec(right, environment)?,
                        ),
                        byte_width: element_type.byte_width(),
                    });
                }
                if let Some(element_type) = self.contract_pointer_element_type(right, environment) {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_contract_expression_to_spec(right, environment)?,
                        ),
                        elements: Box::new(
                            self.lower_contract_expression_to_spec(left, environment)?,
                        ),
                        byte_width: element_type.byte_width(),
                    });
                }
                Ok(SpecExpression::Add(
                    Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                    Box::new(self.lower_contract_expression_to_spec(right, environment)?),
                ))
            }
            ContractExpression::Subtract(left, right) => {
                if let Some(element_type) = self.contract_pointer_element_type(left, environment)
                    && self
                        .contract_pointer_element_type(right, environment)
                        .is_none()
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_contract_expression_to_spec(left, environment)?,
                        ),
                        elements: Box::new(SpecExpression::Subtract(
                            Box::new(SpecExpression::Value(int32(0))),
                            Box::new(self.lower_contract_expression_to_spec(right, environment)?),
                        )),
                        byte_width: element_type.byte_width(),
                    });
                }
                Ok(SpecExpression::Subtract(
                    Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                    Box::new(self.lower_contract_expression_to_spec(right, environment)?),
                ))
            }
            ContractExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_contract_expression_to_spec(expression, environment)?,
            ))),
            ContractExpression::Index(base, index) => {
                let array_ref = self.lower_array_ref_to_spec(base, environment)?;
                let index = self.lower_contract_expression_to_spec(index, environment)?;
                Ok(SpecExpression::MemoryLoad {
                    memory: array_ref.memory,
                    pointer: Box::new(SpecExpression::PointerOffset {
                        pointer: Box::new(array_ref.pointer),
                        elements: Box::new(index),
                        byte_width: array_ref.element_type.byte_width(),
                    }),
                    value_type: array_ref.element_type,
                })
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => Ok(SpecExpression::If {
                condition: Box::new(
                    self.click_proposition_to_spec_proposition(condition, environment)?,
                ),
                then_branch: Box::new(
                    self.lower_contract_expression_to_spec(then_branch, environment)?,
                ),
                else_branch: Box::new(
                    self.lower_contract_expression_to_spec(else_branch, environment)?,
                ),
            }),
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    accumulator.clone(),
                    SpecExpression::CExpression(CExpression::Variable(accumulator.clone())),
                );
                body_environment.values.insert(
                    item.clone(),
                    SpecExpression::CExpression(CExpression::Variable(item.clone())),
                );
                Ok(SpecExpression::RangeFold {
                    start: Box::new(self.lower_contract_expression_to_spec(start, environment)?),
                    end: Box::new(self.lower_contract_expression_to_spec(end, environment)?),
                    initial: Box::new(
                        self.lower_contract_expression_to_spec(initial, environment)?,
                    ),
                    accumulator: accumulator.clone(),
                    item: item.clone(),
                    body: Box::new(
                        self.lower_contract_expression_to_spec(body, &body_environment)?,
                    ),
                })
            }
            ContractExpression::Let {
                name,
                c_type,
                value,
                body,
            } => {
                let value = self.lower_contract_expression_to_spec(value, environment)?;
                if let (Some(c_type), SpecExpression::Value(fixed)) = (c_type, &value) {
                    if !c_value_matches_click_type(fixed, *c_type) {
                        return Err(format!(
                            "let binding `{name}` evaluated to {fixed:?}, which does not match {c_type:?}"
                        ));
                    }
                }
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::CExpression(CExpression::Variable(name.clone())),
                );
                Ok(SpecExpression::Let {
                    name: name.clone(),
                    value: Box::new(value),
                    body: Box::new(
                        self.lower_contract_expression_to_spec(body, &body_environment)?,
                    ),
                })
            }
            ContractExpression::Call { name, arguments } => {
                self.lower_click_function_call_to_spec(name, arguments, environment)
            }
        }
    }

    fn spec_segment_environment(
        &self,
        segment: &ContractSegment,
        environment: &SpecElaborationContext,
    ) -> Result<SpecElaborationContext, String> {
        match segment.state {
            ContractSegmentState::Current => Ok(environment.clone()),
            ContractSegmentState::Old => {
                environment.old_state(&self.entry_values, self.entry_state.memory())
            }
        }
    }

    fn contract_segment_element_width(
        &self,
        segment: &ContractSegment,
        environment: &SpecElaborationContext,
    ) -> u32 {
        self.c_expression_array_element_type(&segment.base, environment)
            .unwrap_or(CType::Int32)
            .byte_width()
    }

    fn lower_contract_segment_base_to_spec(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        self.lower_c_fragment_to_spec(expression, environment)
    }

    fn lower_resource_subject_to_spec(
        &mut self,
        resource: &ResourceSubject,
        environment: &SpecElaborationContext,
    ) -> Result<SpecResource, String> {
        match resource {
            ResourceSubject::Memory(segment) => {
                let environment = self.spec_segment_environment(segment, environment)?;
                Ok(SpecResource::Memory {
                    base: self.lower_contract_segment_base_to_spec(&segment.base, &environment)?,
                    start: self.lower_c_fragment_to_spec(&segment.start, &environment)?,
                    end: self.lower_c_fragment_to_spec(&segment.end, &environment)?,
                    element_width: self.contract_segment_element_width(segment, &environment),
                })
            }
            ResourceSubject::Declared {
                kind,
                name,
                arguments,
                ..
            } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.lower_contract_expression_to_spec(argument, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match kind {
                    ResourceKind::Composite => SpecResource::Composite {
                        name: name.clone(),
                        arguments,
                    },
                    ResourceKind::Token => SpecResource::Token {
                        name: name.clone(),
                        arguments,
                    },
                })
            }
        }
    }

    /// The elaboration context of a state a proof recorded under `selector`:
    /// its locals are fixed values and its memory is fixed, so the kernel
    /// lowers loads there exactly as the proof observed them.
    fn snapshot_environment(
        &self,
        selector: &SnapshotSelector,
        environment: &SpecElaborationContext,
    ) -> Option<SpecElaborationContext> {
        let state = self.snapshots?.get(selector)?;
        let mut values = environment.values.clone();
        values.extend(
            state
                .locals()
                .object_values()
                .map(|(name, value)| (name.to_string(), SpecExpression::Value(value.clone()))),
        );
        let array_refs = state
            .locals()
            .array_object_values()
            .map(|(name, value, element_type)| {
                (
                    name.to_string(),
                    SpecArrayRef {
                        memory: SpecMemory::Fixed(state.memory().clone()),
                        pointer: SpecExpression::Value(value.clone()),
                        element_type,
                    },
                )
            })
            .collect();
        Some(SpecElaborationContext {
            values,
            array_refs,
            current_memory: SpecMemory::Fixed(state.memory().clone()),
            current_loop_entry: None,
            function_contract: false,
            at_function_entry: false,
            snapshot_state: Some(state.clone()),
        })
    }

    fn lower_at_expression_to_spec(
        &mut self,
        selector: &SnapshotSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        if let Some(snapshot) = self.snapshot_environment(selector, environment) {
            return self.lower_contract_expression_to_spec(expression, &snapshot);
        }
        match self.resolve_visit_selector(selector)? {
            ResolvedProgramPoint::Current => {
                self.lower_contract_expression_to_spec(expression, environment)
            }
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                Ok(SpecExpression::LoopEntrySnapshot(Box::new(
                    self.lower_contract_expression_to_spec(expression, environment)?,
                )))
            }
        }
    }

    fn resolve_visit_selector(
        &self,
        selector: &SnapshotSelector,
    ) -> Result<ResolvedProgramPoint, String> {
        match selector {
            SnapshotSelector::ProgramPoint(program_point)
                if self.branch_join_target == Some(program_point) =>
            {
                Ok(ResolvedProgramPoint::Current)
            }
            SnapshotSelector::ProgramPoint(program_point) => {
                self.resolve_program_point_ref(program_point)
            }
            SnapshotSelector::Mark(name) if self.snapshots.is_some() => Err(format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )),
            SnapshotSelector::Mark(name) => Err(format!(
                "proof-local mark `{name}` is available only in an execution proof"
            )),
        }
    }

    fn resolve_program_point_ref(
        &self,
        program_point: &ProgramPointRef,
    ) -> Result<ResolvedProgramPoint, String> {
        let region = self.resolve_code_region_ref(&program_point.region)?;
        match (region, program_point.kind) {
            (CodeRegion::Function, ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::FunctionEntry)
            }
            (CodeRegion::Loop(index), ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::LoopEntry(index))
            }
            (CodeRegion::Function, ProgramPointKind::Exit) => {
                Err("`at(function.exit, ...)` is not supported yet".to_string())
            }
            (CodeRegion::Loop(_), ProgramPointKind::Exit) | (CodeRegion::Statement(_), _)
                if self.snapshots.is_some() =>
            {
                Err(format!(
                    "no state snapshot was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                    crate::surface::diagnostics::describe_program_point_ref(program_point)
                ))
            }
            (CodeRegion::Loop(index), ProgramPointKind::Exit) => Err(format!(
                "`at(loop({index}).exit, ...)` requires a recorded snapshot in an execution proof"
            )),
            (CodeRegion::Statement(_), _) => Err(format!(
                "`at({}, ...)` is not supported in this context yet",
                crate::surface::diagnostics::describe_program_point_ref(program_point)
            )),
        }
    }

    fn resolve_code_region_ref(&self, region_ref: &CodeRegionRef) -> Result<CodeRegion, String> {
        match region_ref {
            CodeRegionRef::Function => Ok(CodeRegion::Function),
            CodeRegionRef::Loop(index) => Ok(CodeRegion::Loop(*index)),
            CodeRegionRef::Statement(index) => Ok(CodeRegion::Statement(*index)),
            CodeRegionRef::Label(label) => self
                .structural_clauses
                .iter()
                .find(|clause| clause.label() == Some(label.as_str()))
                .map(|clause| *clause.region())
                .ok_or_else(|| format!("unknown code region label `{label}`")),
        }
    }

    fn lower_c_fragment_to_spec(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(SpecExpression::Value(value.clone())),
            CExpression::Variable(name) => match environment.values.get(name) {
                Some(value) => Ok(value.clone()),
                None if self.entry_state.global_object_type(name).is_some() => {
                    Ok(SpecExpression::MemoryLoad {
                        memory: environment.current_memory.clone(),
                        pointer: Box::new(SpecExpression::CExpression(CExpression::AddressOf(
                            Box::new(CExpression::Variable(name.clone())),
                        ))),
                        value_type: self
                            .entry_state
                            .global_object_type(name)
                            .expect("checked global object type"),
                    })
                }
                None if matches!(environment.current_memory, SpecMemory::Fixed(_)) => {
                    if name == "result" {
                        Err("`result` is not available inside `old(...)`".to_string())
                    } else {
                        Err(format!("unknown old-state variable `{name}`"))
                    }
                }
                None => Ok(SpecExpression::CExpression(CExpression::Variable(
                    name.clone(),
                ))),
            },
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                Ok(SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                    elements: Box::new(SpecExpression::Value(int32(*bytes))),
                    byte_width: 1,
                })
            }
            // Arithmetic on a pointer offsets it by whole elements, as C does.
            CExpression::Add(left, right) => {
                if let Some(element_type) = self.c_expression_array_element_type(left, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                        elements: Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                        byte_width: element_type.byte_width(),
                    });
                }
                if let Some(element_type) = self.c_expression_array_element_type(right, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                        elements: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                        byte_width: element_type.byte_width(),
                    });
                }
                Ok(SpecExpression::Add(
                    Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                    Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                ))
            }
            CExpression::Subtract(left, right) => {
                if let Some(element_type) = self.c_expression_array_element_type(left, environment)
                {
                    if self
                        .c_expression_array_element_type(right, environment)
                        .is_none()
                    {
                        return Ok(SpecExpression::PointerOffset {
                            pointer: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                            elements: Box::new(SpecExpression::Subtract(
                                Box::new(SpecExpression::Value(int32(0))),
                                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                            )),
                            byte_width: element_type.byte_width(),
                        });
                    }
                }
                Ok(SpecExpression::Subtract(
                    Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                    Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                ))
            }
            CExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_c_fragment_to_spec(expression, environment)?,
            ))),
            CExpression::Index(base, index) => {
                let element_type = self
                    .c_expression_array_element_type(base, environment)
                    .unwrap_or(CType::Int32);
                let pointer = SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(base, environment)?),
                    elements: Box::new(self.lower_c_fragment_to_spec(index, environment)?),
                    byte_width: element_type.byte_width(),
                };
                Ok(SpecExpression::MemoryLoad {
                    memory: environment.current_memory.clone(),
                    pointer: Box::new(pointer),
                    value_type: element_type,
                })
            }
            CExpression::TypedLoad {
                pointer,
                value_type: CType::Int32Array(_) | CType::UInt8Array(_),
            } => self.lower_c_fragment_to_spec(pointer, environment),
            CExpression::TypedLoad {
                pointer,
                value_type,
            } => Ok(SpecExpression::MemoryLoad {
                memory: environment.current_memory.clone(),
                pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                value_type: *value_type,
            }),
            CExpression::Load(pointer) => Ok(SpecExpression::MemoryLoad {
                memory: environment.current_memory.clone(),
                pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                value_type: CType::Int32,
            }),
            expression => Ok(SpecExpression::CExpression(expression.clone())),
        }
    }

    fn lower_click_function_call_to_spec(
        &mut self,
        name: &str,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let definition = self
            .click_function_environment
            .get(name)
            .ok_or_else(|| format!("unknown function `{name}`"))?;
        if arguments.len() != definition.parameters().len() {
            return Err(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                arguments.len()
            ));
        }

        if self.opaque_click_functions.contains(name) {
            return Ok(SpecExpression::PureFunctionApplication {
                name: name.to_string(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.lower_contract_expression_to_spec(argument, environment))
                    .collect::<Result<Vec<_>, _>>()?,
            });
        }
        if self.active_click_functions.contains(name) {
            if definition.decreases().is_none() {
                return Err(format!(
                    "recursive function call `{name}` has no decreases measure"
                ));
            }
            return Ok(SpecExpression::PureFunctionApplication {
                name: name.to_string(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.lower_contract_expression_to_spec(argument, environment))
                    .collect::<Result<Vec<_>, _>>()?,
            });
        }

        let mut function_environment =
            SpecElaborationContext::with_current_memory(environment.current_memory.clone());
        for (parameter, argument) in definition.parameters().iter().zip(arguments) {
            if parameter_is_click_array_ref(parameter) {
                let expected_element_type = click_array_element_type(parameter.c_type())
                    .ok_or_else(|| {
                        format!(
                            "function `{}` parameter `{}` is not an array-ref parameter",
                            definition.name(),
                            parameter.name()
                        )
                    })?;
                let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                if array_ref.element_type != expected_element_type {
                    return Err(format!(
                        "function `{}` parameter `{}` expects {:?} array elements, got {:?}",
                        definition.name(),
                        parameter.name(),
                        expected_element_type,
                        array_ref.element_type
                    ));
                }
                function_environment
                    .array_refs
                    .insert(parameter.name().to_string(), array_ref);
            } else {
                function_environment.values.insert(
                    parameter.name().to_string(),
                    self.lower_contract_expression_to_spec(argument, environment)?,
                );
            }
        }

        self.active_click_functions.insert(name.to_string());
        let result =
            self.lower_contract_expression_to_spec(definition.body(), &function_environment);
        self.active_click_functions.remove(name);
        result
    }

    fn lower_array_ref_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        match expression {
            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_array_ref_to_spec(selector, expression, environment),
            ContractExpression::CFragment(CExpression::Variable(name)) => {
                if let Some(array_ref) = environment.array_refs.get(name) {
                    return Ok(array_ref.clone());
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_c_fragment_to_spec(
                        &CExpression::Variable(name.clone()),
                        environment,
                    )?,
                    element_type: self
                        .array_ref_element_type_for_name_in_environment(name, environment),
                })
            }
            ContractExpression::Add(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                if let Ok(array_ref) = self.lower_array_ref_to_spec(right, environment) {
                    let offset = self.lower_contract_expression_to_spec(left, environment)?;
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            ContractExpression::Subtract(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let negative_offset = SpecExpression::Subtract(
                        Box::new(SpecExpression::Value(CValue::Int32(
                            Bitvector32Term::Constant(0),
                        ))),
                        Box::new(offset),
                    );
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(negative_offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            _ => Ok(SpecArrayRef {
                memory: environment.current_memory.clone(),
                pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                element_type: self.contract_array_element_type(expression, environment),
            }),
        }
    }

    fn lower_at_array_ref_to_spec(
        &mut self,
        selector: &SnapshotSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        if let Some(snapshot) = self.snapshot_environment(selector, environment) {
            return self.lower_array_ref_to_spec(expression, &snapshot);
        }
        match self.resolve_visit_selector(selector)? {
            ResolvedProgramPoint::Current => self.lower_array_ref_to_spec(expression, environment),
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                let SpecArrayRef {
                    memory,
                    pointer,
                    element_type,
                } = self.lower_array_ref_to_spec(expression, environment)?;
                let memory = match memory {
                    SpecMemory::Current => SpecMemory::LoopEntry,
                    memory => memory,
                };
                Ok(SpecArrayRef {
                    memory,
                    pointer: SpecExpression::LoopEntrySnapshot(Box::new(pointer)),
                    element_type,
                })
            }
        }
    }

    fn array_ref_element_type_for_name_in_environment(
        &self,
        name: &str,
        environment: &SpecElaborationContext,
    ) -> CType {
        self.parameter_array_element_types
            .get(name)
            .copied()
            .or_else(|| {
                (name == "result")
                    .then(|| self.result_type.pointee_type())
                    .flatten()
            })
            .or_else(|| self.entry_state.global_array_element_type(name))
            .or_else(|| {
                environment.values.get(name).and_then(|value| match value {
                    SpecExpression::Value(CValue::Pointer(pointer)) => {
                        pointer.c_type().pointee_type()
                    }
                    _ => None,
                })
            })
            .unwrap_or(CType::Int32)
    }

    fn contract_array_element_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> CType {
        match expression {
            ContractExpression::CFragment(CExpression::Variable(name)) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .unwrap_or_else(|| {
                    self.array_ref_element_type_for_name_in_environment(name, environment)
                }),
            ContractExpression::Field { lowered, .. } => self
                .c_expression_array_element_type(lowered, environment)
                .unwrap_or(CType::Int32),
            ContractExpression::At { expression, .. } => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Old(expression) => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Add(left, right) => {
                let left_type = self.contract_array_element_type(left, environment);
                if left_type != CType::Int32 {
                    return left_type;
                }
                self.contract_array_element_type(right, environment)
            }
            ContractExpression::Subtract(left, _) => {
                self.contract_array_element_type(left, environment)
            }
            _ => CType::Int32,
        }
    }

    /// The element type a contract expression steps by when it is a pointer:
    /// an array reference or a pointer-valued binding in scope, a pointer
    /// fragment, or pointer arithmetic on one. `None` for a scalar.
    fn contract_pointer_element_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Option<CType> {
        match expression {
            ContractExpression::CBinding(name) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .or_else(|| {
                    environment.values.get(name).and_then(|value| match value {
                        SpecExpression::Value(CValue::Pointer(pointer)) => {
                            pointer.c_type().pointee_type()
                        }
                        _ => None,
                    })
                }),
            ContractExpression::CFragment(expression)
            | ContractExpression::Field {
                lowered: expression,
                ..
            } => self.c_expression_array_element_type(expression, environment),
            ContractExpression::Old(expression) | ContractExpression::At { expression, .. } => {
                self.contract_pointer_element_type(expression, environment)
            }
            ContractExpression::Add(left, right) => self
                .contract_pointer_element_type(left, environment)
                .or_else(|| self.contract_pointer_element_type(right, environment)),
            ContractExpression::Subtract(left, _) => {
                self.contract_pointer_element_type(left, environment)
            }
            _ => None,
        }
    }

    fn c_expression_array_element_type(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Option<CType> {
        match expression {
            CExpression::Variable(name) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .or_else(|| self.parameter_array_element_types.get(name).copied())
                .or_else(|| {
                    (name == "result")
                        .then(|| self.result_type.pointee_type())
                        .flatten()
                })
                .or_else(|| self.entry_state.global_array_element_type(name))
                .or_else(|| {
                    environment.values.get(name).and_then(|value| match value {
                        SpecExpression::Value(CValue::Pointer(pointer)) => {
                            pointer.c_type().pointee_type()
                        }
                        _ => None,
                    })
                }),
            CExpression::TypedLoad { value_type, .. } => match value_type {
                CType::Int32Array(_) => Some(CType::Int32),
                CType::UInt8Array(_) => Some(CType::UInt8),
                value_type => value_type.pointee_type(),
            },
            CExpression::PointerOffsetBytes { pointer, .. } => {
                self.c_expression_array_element_type(pointer, environment)
            }
            CExpression::Add(left, right) => self
                .c_expression_array_element_type(left, environment)
                .or_else(|| self.c_expression_array_element_type(right, environment)),
            CExpression::Subtract(left, _) => {
                self.c_expression_array_element_type(left, environment)
            }
            _ => None,
        }
    }

    fn lower_current_invariant_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(CExpression::Value(value.clone())),
            CExpression::Variable(name) => Ok(self
                .quantified_values
                .get(name)
                .cloned()
                .map(CExpression::Value)
                .unwrap_or_else(|| CExpression::Variable(name.clone()))),
            CExpression::AddressOf(expression) => Ok(CExpression::AddressOf(Box::new(
                self.lower_current_invariant_c_expression(expression)?,
            ))),
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                Ok(CExpression::PointerOffsetBytes {
                    pointer: Box::new(self.lower_current_invariant_c_expression(pointer)?),
                    bytes: *bytes,
                })
            }
            CExpression::Add(left, right) => Ok(CExpression::Add(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Divide(left, right) => Ok(CExpression::Divide(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
                self.lower_current_invariant_c_expression(expression)?,
            ))),
            CExpression::Load(pointer) => Ok(CExpression::Load(Box::new(
                self.lower_current_invariant_c_expression(pointer)?,
            ))),
            CExpression::TypedLoad {
                pointer,
                value_type,
            } => Ok(CExpression::TypedLoad {
                pointer: Box::new(self.lower_current_invariant_c_expression(pointer)?),
                value_type: *value_type,
            }),
            CExpression::Index(base, index) => Ok(CExpression::Index(
                Box::new(self.lower_current_invariant_c_expression(base)?),
                Box::new(self.lower_current_invariant_c_expression(index)?),
            )),
            expression => Err(format!(
                "unsupported expression in loop invariant: `{expression:?}`"
            )),
        }
    }

    fn loop_effect_checks(
        &self,
        loop_index: usize,
        body: &syntax::C0Statement,
    ) -> Result<Vec<CLoopEffectCheck>, ClickError> {
        let modified_locals = c0_loop_modified_locals(body);
        let mut checks = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.is_effect_kind())
            .enumerate()
            .map(|(item_index, item)| {
                let effect = item
                    .effect()
                    .expect("effect structural item should contain an effect");
                let span = match item.kind() {
                    StructuralItemKind::Effect => CLoopEffectSpan::Whole,
                    StructuralItemKind::StepEffect => CLoopEffectSpan::Step,
                    _ => unreachable!("loop effect filter should only include effect items"),
                };
                let lowered = self
                    .lower_loop_effect(effect, span, &modified_locals)
                    .map_err(|message| {
                        ClickError::new(format!("loop {loop_index} effect {item_index}: {message}"))
                    })?;
                let context = match effect {
                    Effect::Immutable => match span {
                        CLoopEffectSpan::Whole => {
                            format!("loop {loop_index} immutable {item_index}")
                        }
                        CLoopEffectSpan::Step => {
                            format!("loop {loop_index} step immutable {item_index}")
                        }
                    },
                    Effect::Mutable(_) => match span {
                        CLoopEffectSpan::Whole => {
                            format!("loop {loop_index} mutable {item_index}")
                        }
                        CLoopEffectSpan::Step => {
                            format!("loop {loop_index} step mutable {item_index}")
                        }
                    },
                };
                Ok(CLoopEffectCheck::new_with_span(
                    lowered,
                    span,
                    Some(context),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let function_mutable = self
            .function_effects
            .iter()
            .flat_map(|clause| match clause.effect() {
                Effect::Mutable(segments) => segments.clone(),
                Effect::Immutable => Vec::new(),
            })
            .collect::<Vec<_>>();
        let has_explicit_whole_effect = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .any(|item| item.kind() == StructuralItemKind::Effect);
        if self.function_effects.is_empty()
            && !has_explicit_whole_effect
            && !self.implicit_contract_mutable_segments.is_empty()
        {
            checks.push(CLoopEffectCheck::new_with_span(
                CLoopEffect::Mutable(self.implicit_contract_mutable_segments.to_vec()),
                CLoopEffectSpan::Whole,
                Some(format!("loop {loop_index} inherited owned resource frame")),
            ));
        }
        let implicit_effect = if !function_mutable.is_empty() {
            Some(Effect::Mutable(function_mutable))
        } else if self
            .function_effects
            .iter()
            .any(|clause| matches!(clause.effect(), Effect::Immutable))
        {
            Some(Effect::Immutable)
        } else {
            None
        };
        if let Some(effect) = implicit_effect {
            let lowered = self
                .lower_loop_effect(&effect, CLoopEffectSpan::Whole, &modified_locals)
                .map_err(|message| {
                    ClickError::new(format!(
                        "loop {loop_index} inherited function effect: {message}"
                    ))
                })?;
            checks.push(CLoopEffectCheck::new_with_span(
                lowered,
                CLoopEffectSpan::Whole,
                Some(format!("loop {loop_index} inherited function effect")),
            ));
        }
        Ok(checks)
    }

    fn lower_loop_effect(
        &self,
        effect: &Effect,
        span: CLoopEffectSpan,
        modified_locals: &BTreeSet<String>,
    ) -> Result<CLoopEffect, String> {
        match effect {
            Effect::Immutable => Ok(CLoopEffect::Immutable),
            Effect::Mutable(segments) => segments
                .iter()
                .map(|segment| {
                    if segment.state != ContractSegmentState::Current {
                        return Err(
                            "`mutable` inside `loop` expects current-state segments; `old(...)` is not supported here"
                                .to_string(),
                        );
                    }
                    if span == CLoopEffectSpan::Whole {
                        let names = contract_segment_referenced_names(segment);
                        if let Some(name) = names.iter().find(|name| modified_locals.contains(*name))
                        {
                            return Err(format!(
                                "whole-loop `mutable` segment references loop-modified local `{name}`; use `step {{ ... }}` for iteration-relative effects or state a stable whole-loop range"
                            ));
                        }
                    }
                    Ok(CMemorySegment::new(
                        self.lower_current_invariant_c_expression(&segment.base)?,
                        self.lower_current_invariant_c_expression(&segment.start)?,
                        self.lower_current_invariant_c_expression(&segment.end)?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()
                .map(CLoopEffect::Mutable),
        }
    }
}
