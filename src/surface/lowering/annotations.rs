use super::*;
use crate::kernel::{AlgebraicTerm, AlgebraicTermNode};

fn integer_comparison_operator(
    operator: ComparisonOperator,
) -> Result<crate::kernel::IntegerComparisonOperator, String> {
    Ok(match operator {
        ComparisonOperator::Equal => crate::kernel::IntegerComparisonOperator::Equal,
        ComparisonOperator::NotEqual => crate::kernel::IntegerComparisonOperator::NotEqual,
        ComparisonOperator::LessThan => crate::kernel::IntegerComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => crate::kernel::IntegerComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => crate::kernel::IntegerComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => crate::kernel::IntegerComparisonOperator::GreaterEqual,
        ComparisonOperator::In => return Err("Integer expressions do not support `in`".to_string()),
    })
}

fn is_unsuffixed_integer_literal_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::IntegerLiteral(_) => true,
        ContractExpression::Negate(inner) => is_unsuffixed_integer_literal_expression(inner),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            is_unsuffixed_integer_literal_expression(left)
                && is_unsuffixed_integer_literal_expression(right)
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests;

pub(in crate::surface) fn check_resource_field_schemas(
    file: &mut ClickFile,
) -> Result<(), ClickError> {
    if file
        .resource_definitions
        .iter()
        .all(ResourceDefinition::is_countable)
    {
        return Ok(());
    }
    let environment = ClickFunctionEnvironment::with_algebraic_types(
        &[],
        &super::super::validation::combined_algebraic_type_definitions(file)?,
    );
    for definition in &mut file.resource_definitions {
        if definition.is_countable() {
            continue;
        }
        let fields = definition
            .fields()
            .iter()
            .map(|field| {
                let ty = match field.click_type() {
                    ClickType::C(ty) => crate::kernel::ResourceFieldType::C(ty.to_kernel_type()),
                    ClickType::Algebraic(application) => {
                        crate::kernel::ResourceFieldType::Algebraic(
                            algebraic_kernel_type(&environment, application)
                                .map_err(ClickError::new)?,
                        )
                    }
                    ClickType::Parameter(name) => {
                        return Err(ClickError::new(format!(
                            "unresolved resource field type `{name}`"
                        )));
                    }
                    ClickType::Integer => crate::kernel::ResourceFieldType::Integer,
                };
                Ok((field.name().to_string(), ty))
            })
            .collect::<Result<Vec<_>, ClickError>>()?;
        definition.field_schema = Some(
            crate::kernel::ResourceFieldSchema::new(fields).ok_or_else(|| {
                ClickError::new(format!(
                    "invalid field schema for resource `{}`",
                    definition.name()
                ))
            })?,
        );
    }
    let schemas = file
        .resource_definitions
        .iter()
        .filter_map(|definition| {
            definition
                .field_schema()
                .map(|schema| (definition.name().to_string(), schema.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    // Separate from the existing C/spec and composite-witness ranges. These
    // variables are collected from the entry resource state by the kernel's
    // fresh-variable allocator, so later execution cannot reuse their IDs.
    let mut next_field_variable = 9_000_000_000u64;
    for contract in &mut file.contract_definitions {
        for parameter in contract.proof_parameters.iter_mut().flatten() {
            let ResourceClause::Named { binding, resource } = parameter else {
                unreachable!()
            };
            let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                unreachable!()
            };
            binding.schema = Some(
                schemas
                    .get(name)
                    .ok_or_else(|| {
                        ClickError::new("resource proof parameter has no checked schema")
                    })?
                    .clone(),
            );
        }
    }
    for function in file.function_blocks.iter_mut().chain(
        file.contract_definitions
            .iter_mut()
            .map(|contract| &mut contract.function_block),
    ) {
        let mut bindings = BTreeMap::new();
        let parameter_names = function
            .signature
            .parameters()
            .iter()
            .map(|parameter| parameter.name())
            .collect::<BTreeSet<_>>();
        for requirement in &mut function.requires {
            let Requirement::Resource(ResourceClause::Named { binding, resource }) = requirement
            else {
                continue;
            };
            if parameter_names.contains(binding.name.as_str()) {
                return Err(ClickError::new(format!(
                    "resource instance `{}` conflicts with a C parameter",
                    binding.name
                )));
            }
            let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                return Err(ClickError::new(
                    "named ownership requires a declared resource",
                ));
            };
            let schema = schemas
                .get(name)
                .ok_or_else(|| ClickError::new("named resource has no checked fields"))?;
            let fields = schema
                .fields()
                .iter()
                .map(|(_, ty)| {
                    let variable = Variable(next_field_variable);
                    next_field_variable += 1;
                    match ty {
                        crate::kernel::ResourceFieldType::Integer => {
                            AlgebraicValue::Integer(crate::kernel::IntegerTerm::Variable(variable))
                        }
                        crate::kernel::ResourceFieldType::C(ty) => {
                            AlgebraicValue::C(crate::kernel::symbolic_call_result(*ty, variable))
                        }
                        crate::kernel::ResourceFieldType::Algebraic(ty) => {
                            AlgebraicValue::Algebraic(AlgebraicTerm {
                                algebraic_type: ty.clone(),
                                node: AlgebraicTermNode::Variable(variable),
                            })
                        }
                    }
                })
                .collect::<crate::kernel::ResourceArguments>();
            binding.schema = Some(schema.clone());
            binding.fields = Some(fields);
            bindings.insert(binding.identity, binding.clone());
        }
        for ensure in &mut function.ensures {
            if let Ensure::Resource(ResourceClause::Named { binding, resource }) =
                &mut ensure.ensure
            {
                if let Some(entry) = bindings.get(&binding.identity) {
                    *binding = entry.clone();
                } else {
                    let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                        unreachable!()
                    };
                    binding.schema = Some(
                        schemas
                            .get(name)
                            .ok_or_else(|| ClickError::new("returned resource has no schema"))?
                            .clone(),
                    );
                }
            }
        }
    }
    Ok(())
}

fn contract_expression_is_sequence(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => true,
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => contract_expression_is_sequence(inner),
        _ => false,
    }
}
fn contract_expression_is_algebraic(
    expression: &ContractExpression,
    functions: &ClickFunctionEnvironment,
    environment: &SpecElaborationContext,
    lexical_bindings: &mut Vec<(String, bool)>,
) -> bool {
    match expression {
        ContractExpression::ResourceField(access) => {
            matches!(access.click_type, Some(ClickType::Algebraic(_)))
        }
        ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicVariable { .. } => true,
        ContractExpression::Binding(name) => lexical_bindings
            .iter()
            .rev()
            .find_map(|(binding, algebraic)| (binding == name).then_some(*algebraic))
            .unwrap_or_else(|| environment.algebraic_values.contains_key(name)),
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => contract_expression_is_algebraic(inner, functions, environment, lexical_bindings),
        ContractExpression::AlgebraicMatch { arms, .. } => arms.first().is_some_and(|arm| {
            contract_expression_is_algebraic(&arm.body, functions, environment, lexical_bindings)
        }),
        ContractExpression::Let {
            name, value, body, ..
        } => {
            let value_is_algebraic =
                contract_expression_is_algebraic(value, functions, environment, lexical_bindings);
            lexical_bindings.push((name.clone(), value_is_algebraic));
            let result =
                contract_expression_is_algebraic(body, functions, environment, lexical_bindings);
            lexical_bindings.pop();
            result
        }
        ContractExpression::Call { name, .. } if name == "to_nat" => true,
        ContractExpression::Call { name, .. } => functions
            .get(name)
            .is_some_and(|definition| matches!(definition.return_type(), ClickType::Algebraic(_))),
        _ => false,
    }
}
use crate::kernel::CFloatClassification;
use crate::kernel::CPredicateUnfolding;
use crate::kernel::SpecSequenceExpression;
use crate::kernel::{
    AlgebraicSchemas, AlgebraicType, AlgebraicValueType, AlgebraicVariantType,
    SpecAlgebraicExpression, SpecAlgebraicExpressionNode, SpecAlgebraicResultMatchArm,
    SpecAlgebraicValue,
};

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
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
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
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
        branch_join_target: None,
        snapshots: None,
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
    lower_composite_resource_facts_with_bindings(
        definition,
        predicate_environment,
        click_function_environment,
        &[],
    )
}

pub(in crate::surface) fn lower_composite_resource_facts_with_bindings(
    definition: &ResourceDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    bindings: &[(String, ClickType)],
) -> Result<Vec<SpecProposition>, ClickError> {
    let body = definition
        .composite_body()
        .expect("only composite definitions have logical facts");
    let entry_state = CState::new();
    let mut lowerer = AnnotationLowerer {
        structural_clauses: &[],
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
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
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
        branch_join_target: None,
        snapshots: None,
        count_assumptions: None,
    };
    let all_predicates = predicate_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let mut facts = Vec::new();
    for (name, ty) in bindings {
        if let ClickType::Algebraic(application) = ty {
            lowerer.algebraic_variables.insert(
                name.clone(),
                SpecAlgebraicExpression {
                    algebraic_type: algebraic_kernel_type(click_function_environment, application)
                        .map_err(ClickError::new)?,
                    node: SpecAlgebraicExpressionNode::Binding(name.clone()),
                },
            );
        }
    }
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
) -> Result<CFunction, ClickError> {
    let (resource_requires, resource_ensures, borrowed_resource_ensures) =
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
    // `consumes` grants the callee a write-capable owned range. Carry that
    // frame into loop summaries so checked proof artifacts retain the same
    // memory-footprint evidence as independent contract certification.
    let implicit_contract_mutable_segments = contract_mutable.as_slice();
    let resource_derived_mutable_frame = !contract_mutable.is_empty()
        || function_block
            .requires()
            .iter()
            .any(|requirement| matches!(requirement.inner(), Requirement::Resource(_)));
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        implicit_contract_mutable_segments,
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: resource_derived_mutable_frame,
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
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_000_000,
        branch_join_target: None,
        snapshots: None,
        count_assumptions: None,
    };
    // Loop-level resource declarations are lowered once, before the body, so
    // every loop reaches its footprint and its body resource context without
    // re-walking the contract.
    let loop_resources = loop_resource_declarations(
        function_block,
        parsed_function,
        resource_environment,
        &mut lowerer,
    )?;
    lowerer.loop_resources = loop_resources;
    let body = lowerer.lower_statement(parsed_function.body())?;
    let parsed_kernel_function = parsed_function.to_kernel_function();
    let source_body = parsed_kernel_function.body().clone();
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
    .with_return_pointee_constant(parsed_function.return_pointee_is_constant())
    .with_source_body(source_body);
    if parsed_kernel_function.is_program_entry() {
        function = function.with_program_entry();
    }
    if let Some(struct_name) = parsed_function.return_struct_name() {
        let layout = parsed_function
            .structs()
            .get(struct_name)
            .expect("struct return has a parsed layout")
            .to_kernel_aggregate_layout();
        function = function.with_return_aggregate_layout(layout);
    }
    let function = function
        .with_global_variables(parsed_kernel_function.global_variables().to_vec())
        .with_global_arrays(parsed_kernel_function.global_arrays().to_vec())
        .with_global_aggregates(parsed_kernel_function.global_aggregates().to_vec())
        .with_global_aggregate_arrays(parsed_kernel_function.global_aggregate_arrays().to_vec())
        .with_static_variables(parsed_kernel_function.static_variables().to_vec())
        .with_static_arrays(parsed_kernel_function.static_arrays().to_vec())
        .with_static_aggregates(parsed_kernel_function.static_aggregates().to_vec())
        .with_static_aggregate_arrays(parsed_kernel_function.static_aggregate_arrays().to_vec())
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
        .with_borrowed_resource_ensures(borrowed_resource_ensures)
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
    if let Some(parameter) =
        crate::kernel::modified_by_value_aggregate_parameter_with_current_ensure_in_source(
            &function,
        )
    {
        return Err(ClickError::new(format!(
            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
        )));
    }
    Ok(if resource_derived_mutable_frame {
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
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
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
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_300_000,
        branch_join_target: Some(branch_join_target),
        snapshots: None,
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
    _opaque_click_functions: BTreeSet<String>,
) -> (AnnotationLowerer<'a>, SpecElaborationContext) {
    let lowerer = AnnotationLowerer {
        structural_clauses: &[],
        predicate_environment,
        click_function_environment,
        entry_state,
        result_type: result.map(CValue::c_type).unwrap_or(CType::Int32),
        entry_values,
        parameter_array_element_types: array_element_types,
        quantified_values: BTreeMap::new(),
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 2_000_000,
        branch_join_target: None,
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        snapshots: Some(snapshots),
        count_assumptions: Some(assumptions),
    };
    // The proof's current locals are fixed values in every context: a name a
    // snapshot or the entry does not bind keeps its current value, as the
    // proof reads it.
    let mut context = SpecElaborationContext {
        values: current_values
            .into_iter()
            .map(|(name, value)| (name, SpecExpression::Value(value)))
            .collect(),
        ..SpecElaborationContext::default()
    };
    if let Some(result) = result {
        context
            .values
            .insert("result".to_string(), SpecExpression::Value(result.clone()));
    }
    (lowerer, context)
}

/// Elaborates a fixed-state proposition with already-elaborated symbolic
/// algebraic and Integer bindings. The bindings are logical values captured at the
/// application site, so entering `old(...)` or another snapshot keeps the
/// same value instead of re-evaluating its source expression there.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
    proposition: &ClickProposition,
    array_element_types: BTreeMap<String, CType>,
    entry_state: &CState,
    entry_values: BTreeMap<String, CValue>,
    current_values: BTreeMap<String, CValue>,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
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
    let mut context = context;
    context.algebraic_values = algebraic_values.into_iter().collect();
    context.integer_values = integer_values.clone();
    lowerer.click_proposition_to_spec_proposition(proposition, &context)
}

/// Elaborates an algebraic expression at a fixed proof state without
/// evaluating or expanding it. This is the symbolic value captured for an
/// algebraic theorem argument.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_algebraic_expression(
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
) -> Result<SpecAlgebraicExpression, String> {
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
    lowerer.lower_contract_algebraic_to_spec(expression, &context)
}

/// Elaborates an Integer expression at a fixed proof state without
/// evaluating or expanding it. This is the symbolic value captured for an
/// Integer theorem argument.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_integer_expression(
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
) -> Result<crate::kernel::SpecIntegerExpression, String> {
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
    lowerer.lower_contract_integer_to_spec(expression, &context)
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
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
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
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
        branch_join_target: None,
        snapshots: None,
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
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
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
        algebraic_variables: BTreeMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
        branch_join_target: None,
        snapshots: None,
        count_assumptions: None,
    };
    let mut context = SpecElaborationContext::for_function_contract();
    // Parameters shadow file-scope spellings in both current and old clauses.
    // Keep them as C bindings, not loads from same-named global storage.
    context
        .values
        .extend(parsed_function.parameters().iter().map(|parameter| {
            let name = parameter.name().to_string();
            (
                name.clone(),
                SpecExpression::CExpression(CExpression::Variable(name)),
            )
        }));
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
        let opaque_predicate = matches!(
            &proposition,
            ClickProposition::PredicateCall { name, .. }
                if predicate_environment.get(name).is_some()
        )
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
        let opaque_predicate = matches!(
            proposition,
            ClickProposition::PredicateCall { name, .. }
                if predicate_environment.get(name).is_some()
        )
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
    {
        if let Some(startup) = &parsed_function.program_entry_state {
            mutable.extend(startup.resources().facts().iter().filter_map(|fact| {
                let range = fact.memory_own_range()?;
                Some(
                    CMemorySegment::new(
                        CExpression::Value(CValue::pointer(range.base().clone())),
                        CExpression::Value(CValue::Int32(range.start().clone())),
                        CExpression::Value(CValue::Int32(range.end().clone())),
                    )
                    .with_element_width(range.element_width()),
                )
            }));
        }
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
    let claims = if function_block.ensures().is_empty() {
        vec![CFunctionContractClaim::body_safety()]
    } else {
        let mut proposition_index = 0;
        let mut resource_index = 0;
        let mut claims = Vec::new();
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
        ClickProposition::FloatClassification { .. } => true,
    }
}

/// Lowers each loop's `owns` and `views` clauses once for the function.
///
/// A loop declaration is the same contract shape as a callee's: the owned
/// memory is the loop's checked write footprint, and the declarations together
/// are the resource context its body executes with.
fn loop_resource_declarations(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
    lowerer: &mut AnnotationLowerer<'_>,
) -> Result<BTreeMap<usize, LoopResourceDeclaration>, ClickError> {
    let mut declarations: BTreeMap<usize, LoopResourceDeclaration> = BTreeMap::new();
    for clause in function_block.structural_clauses() {
        let CodeRegion::Loop(loop_index) = clause.region() else {
            continue;
        };
        if clause.resources().is_empty() {
            continue;
        }
        let declaration = declarations.entry(*loop_index).or_default();
        for resource in clause.resources() {
            collect_owned_resource_memory_segments(
                resource,
                resource_environment,
                parsed_function.parameters(),
                lowerer,
                &mut declaration.owned_segments,
            )?;
            append_entry_resource_specs(
                resource,
                parsed_function.parameters(),
                resource_environment,
                &mut declaration.specs,
            )?;
        }
    }
    Ok(declarations)
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
        ResourceClause::Named { resource, .. } | ResourceClause::Quantified { resource, .. } => {
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

/// A loop's declared resources, lowered once for the enclosing function.
#[derive(Clone, Debug, Default)]
struct LoopResourceDeclaration {
    /// The memory the loop owns, used as its checked whole-loop footprint.
    owned_segments: Vec<CMemorySegment>,
    /// The loop's declarations as kernel resource specs, evaluated at loop
    /// entry to build the body's resource context.
    specs: Vec<CResourceSpec>,
}

struct AnnotationLowerer<'a> {
    structural_clauses: &'a [StructuralClause],
    implicit_contract_mutable_segments: &'a [CMemorySegment],
    /// Resources declared by each loop, keyed by loop index. A loop with a
    /// declaration has the shape of a callee contract: its body executes
    /// owning exactly these resources, and its write footprint is the memory
    /// they own rather than everything the function owns.
    loop_resources: BTreeMap<usize, LoopResourceDeclaration>,
    /// Whether this function's write footprint comes from its resources. A
    /// loop in such a function inherits that footprint, so an empty one is an
    /// inherited empty footprint rather than the absence of one.
    inherits_resource_derived_frame: bool,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    entry_state: &'a CState,
    result_type: CType,
    entry_values: BTreeMap<String, CValue>,
    parameter_array_element_types: BTreeMap<String, CType>,
    quantified_values: BTreeMap<String, CValue>,
    algebraic_variables: BTreeMap<String, SpecAlgebraicExpression>,
    algebraic_types: BTreeMap<(String, Vec<AlgebraicValueType>), AlgebraicType>,
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
}

/// Lower explicit arithmetic evidence without constructing or cloning a C
/// state. Its only environment is the already captured mathematical bindings.
pub(in crate::surface) fn lower_integer_certificate_proposition(
    proposition: &ClickProposition,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
) -> Result<Proposition, String> {
    use crate::kernel::{ConditionTerm, IntegerComparisonOperator, SpecIntegerExpression};
    check_integer_lowering_work(1)?;
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let SpecIntegerExpression::Term(left) =
                lower_contract_integer_to_spec(left, integer_values)?
            else {
                return Err(
                    "machine-backed Integer expressions are not yet certificate atoms".into(),
                );
            };
            let SpecIntegerExpression::Term(right) =
                lower_contract_integer_to_spec(right, integer_values)?
            else {
                return Err(
                    "machine-backed Integer expressions are not yet certificate atoms".into(),
                );
            };
            check_integer_lowering_work(
                integer_root_work(&left).saturating_add(integer_root_work(&right)),
            )?;
            let condition = match integer_comparison_operator(*operator)? {
                IntegerComparisonOperator::Equal => ConditionTerm::integer_equal(left, right),
                IntegerComparisonOperator::NotEqual => {
                    ConditionTerm::integer_not_equal(left, right)
                }
                IntegerComparisonOperator::LessThan => {
                    ConditionTerm::integer_less_than(left, right)
                }
                IntegerComparisonOperator::LessEqual => {
                    ConditionTerm::integer_less_equal(left, right)
                }
                IntegerComparisonOperator::GreaterThan => {
                    ConditionTerm::integer_greater_than(left, right)
                }
                IntegerComparisonOperator::GreaterEqual => {
                    ConditionTerm::integer_greater_equal(left, right)
                }
            };
            Ok(Proposition::ConditionIs(condition, true))
        }
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_integer_certificate_proposition(body, integer_values)?,
        ))),
        _ => Err("an Integer certificate requires a mathematical comparison".into()),
    }
}

pub(in crate::surface) fn lower_contract_integer_to_spec(
    expression: &ContractExpression,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
) -> Result<crate::kernel::SpecIntegerExpression, String> {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    check_integer_lowering_work(1)?;
    match expression {
        ContractExpression::IntegerLiteral(value) => {
            check_integer_lowering_work(value.len().saturating_mul(value.len().saturating_add(4)))?;
            let value = value
                .parse::<num_bigint::BigInt>()
                .map_err(|_| format!("invalid Integer literal `{value}`"))?;
            Ok(SpecIntegerExpression::Term(IntegerTerm::constant(value)))
        }
        ContractExpression::Binding(name) => {
            let value = integer_values
                .get(name)
                .ok_or_else(|| format!("`{name}` is not an Integer binding"))?;
            let SpecIntegerExpression::Term(term) = value else {
                return Err("machine-backed Integer bindings are not yet certificate atoms".into());
            };
            check_integer_lowering_work(integer_root_work(term))?;
            Ok(value.clone())
        }
        ContractExpression::Negate(inner) => {
            let SpecIntegerExpression::Term(term) =
                lower_contract_integer_to_spec(inner, integer_values)?
            else {
                return Err(
                    "machine-backed Integer expressions are not yet certificate atoms".into(),
                );
            };
            check_integer_lowering_work(integer_root_work(&term))?;
            Ok(SpecIntegerExpression::Term(IntegerTerm::negate(term)))
        }
        ContractExpression::Add(left, right) => {
            let left = lower_contract_integer_to_spec(left, integer_values)?;
            let right = lower_contract_integer_to_spec(right, integer_values)?;
            lower_integer_operation(left, right, IntegerOperation::Add)
        }
        ContractExpression::Subtract(left, right) => {
            let left = lower_contract_integer_to_spec(left, integer_values)?;
            let right = lower_contract_integer_to_spec(right, integer_values)?;
            lower_integer_operation(left, right, IntegerOperation::Subtract)
        }
        ContractExpression::Multiply(left, right) => {
            let left = lower_contract_integer_to_spec(left, integer_values)?;
            let right = lower_contract_integer_to_spec(right, integer_values)?;
            lower_integer_operation(left, right, IntegerOperation::Multiply)
        }
        ContractExpression::Let {
            name,
            click_type: Some(ClickType::Integer),
            value,
            body,
        } => {
            let value = lower_contract_integer_to_spec(value, integer_values)?;
            let integer_values = integer_values.with_inserted(name.clone(), value);
            lower_contract_integer_to_spec(body, &integer_values)
        }
        _ => Err("expected a specification-side Integer expression".to_string()),
    }
}

#[derive(Clone, Copy)]
enum IntegerOperation {
    Add,
    Subtract,
    Multiply,
}

fn integer_root_work(term: &crate::kernel::IntegerTerm) -> usize {
    term.as_const().map_or(1, |value| {
        usize::try_from(value.bits())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    })
}

fn check_integer_lowering_work(work: usize) -> Result<(), String> {
    if crate::instrumentation::numeric_operation_work_exceeded(work.max(1)) {
        Err(
            "Integer lowering exceeded the numeric operation or active verification work budget"
                .into(),
        )
    } else {
        Ok(())
    }
}

fn lower_integer_operation(
    left: crate::kernel::SpecIntegerExpression,
    right: crate::kernel::SpecIntegerExpression,
    operation: IntegerOperation,
) -> Result<crate::kernel::SpecIntegerExpression, String> {
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};
    let SpecIntegerExpression::Term(left) = left else {
        return Err("machine-backed Integer expressions are not yet certificate atoms".into());
    };
    let SpecIntegerExpression::Term(right) = right else {
        return Err("machine-backed Integer expressions are not yet certificate atoms".into());
    };
    let work = match operation {
        IntegerOperation::Multiply => {
            integer_root_work(&left).saturating_mul(integer_root_work(&right))
        }
        _ => integer_root_work(&left).saturating_add(integer_root_work(&right)),
    };
    check_integer_lowering_work(work)?;
    let term = match operation {
        IntegerOperation::Add => IntegerTerm::add(left, right),
        IntegerOperation::Subtract => IntegerTerm::subtract(left, right),
        IntegerOperation::Multiply => IntegerTerm::multiply(left, right),
    };
    Ok(SpecIntegerExpression::Term(term))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResolvedProgramPoint {
    Current,
    FunctionEntry,
    LoopEntry(usize),
}

fn spec_argument_to_pure_term(
    argument: &crate::kernel::SpecPureFunctionArgument,
) -> Option<crate::kernel::PureFunctionArgument> {
    match argument {
        crate::kernel::SpecPureFunctionArgument::Integer(expression) => Some(
            crate::kernel::PureFunctionArgument::Integer(spec_integer_to_term(expression)?.into()),
        ),
        crate::kernel::SpecPureFunctionArgument::Value(crate::kernel::SpecExpression::Value(
            value,
        )) => Some(crate::kernel::PureFunctionArgument::Value(value.clone())),
        _ => None,
    }
}

fn spec_integer_to_term(
    expression: &crate::kernel::SpecIntegerExpression,
) -> Option<crate::kernel::IntegerTerm> {
    match expression {
        crate::kernel::SpecIntegerExpression::Term(term) => Some(term.clone()),
        crate::kernel::SpecIntegerExpression::PureFunctionApplication { name, arguments } => {
            Some(crate::kernel::IntegerTerm::PureFunctionApplication(
                crate::kernel::SharedIntegerApplication::intern(
                    name.clone(),
                    arguments
                        .iter()
                        .map(spec_argument_to_pure_term)
                        .collect::<Option<Vec<_>>>()?,
                ),
            ))
        }
        _ => None,
    }
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
                let effect_checks = self.loop_frame_checks(loop_index)?;
                let resource_specs = self.loop_resource_specs(loop_index);
                if matches!(statement, syntax::C0Statement::DoWhile { .. }) {
                    c_do_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_loop_resource_specs(resource_specs)
                } else {
                    c_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_loop_resource_specs(resource_specs)
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
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_frame_checks(loop_index)?;
                let resource_specs = self.loop_resource_specs(loop_index);
                c_seq(
                    lowered_initializer,
                    c_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        crate::kernel::c_for_body_with_step(lowered_body, lowered_step),
                    )
                    .with_loop_resource_specs(resource_specs),
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

    /// The loop's declared resources as kernel specs. An empty list means the
    /// loop declared none and inherits the function's own resource context.
    fn loop_resource_specs(&self, loop_index: usize) -> Vec<CResourceSpec> {
        self.loop_resources
            .get(&loop_index)
            .map(|declaration| declaration.specs.clone())
            .unwrap_or_default()
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
            .enumerate()
            .map(|(item_index, item)| {
                let proposition = unfold_structural_invariant_proposition(
                    self.predicate_environment,
                    item.proposition(),
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

    // Keep recursive connective dispatch separate from large leaf/binder temporaries.
    // Inlining the helpers would put those temporaries back on every nesting level.
    #[inline(never)]
    fn click_proposition_to_spec_proposition(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        #[cfg(test)]
        tests::PROPOSITION_VISITS.with(|visits| visits.set(visits.get() + 1));
        match proposition {
            ClickProposition::At { .. } => {
                self.lower_at_proposition_to_spec(proposition, environment)
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
            ClickProposition::ForAll { .. } => {
                self.lower_for_all_proposition_to_spec(proposition, environment)
            }
            ClickProposition::Exists { .. } => {
                self.lower_exists_proposition_to_spec(proposition, environment)
            }
            ClickProposition::RangeAll { .. } => {
                self.lower_range_all_proposition_to_spec(proposition, environment)
            }
            ClickProposition::RangeAny { .. } => {
                self.lower_range_any_proposition_to_spec(proposition, environment)
            }
            ClickProposition::PredicateCall { .. } => {
                self.lower_predicate_call_proposition_to_spec(proposition, environment)
            }
            ClickProposition::Comparison { .. }
            | ClickProposition::FloatClassification { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::Defined { .. } => {
                self.lower_atomic_proposition_to_spec(proposition, environment)
            }
        }
    }

    #[inline(never)]
    fn lower_at_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
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
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    #[inline(never)]
    fn lower_for_all_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::ForAll {
                click_type: c_type,
                name,
                body,
            } => {
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let c_type = c_type
                    .c_type()
                    .ok_or("only C quantifier binders are currently supported")?
                    .to_kernel_type();
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
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    #[inline(never)]
    fn lower_exists_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::Exists {
                click_type: c_type,
                name,
                body,
            } => {
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let c_type = c_type
                    .c_type()
                    .ok_or("only C quantifier binders are currently supported")?
                    .to_kernel_type();
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
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    #[inline(never)]
    fn lower_range_all_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
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
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    #[inline(never)]
    fn lower_range_any_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
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
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    #[inline(never)]
    fn lower_predicate_call_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::PredicateCall { name, arguments } => {
                if let Some(signature) = self.predicate_environment.contract_signature(name) {
                    let [function] = arguments.as_slice() else {
                        return Err(format!(
                            "contract `{name}` expects one function-pointer argument"
                        ));
                    };
                    let function = match contract_expression_function_address(function) {
                        Some(target) => {
                            SpecExpression::CExpression(CExpression::Value(CValue::typed_pointer(
                                Pointer::function(target.to_string()),
                                signature.to_kernel_type(),
                            )))
                        }
                        None => self.lower_contract_expression_to_spec(function, environment)?,
                    };
                    return Ok(SpecProposition::Predicate {
                        name: CFunctionContract::predicate_name_for(name),
                        arguments: vec![SpecPredicateArgument::Value(function)],
                    });
                }
                let definition = self
                    .predicate_environment
                    .get(name)
                    .ok_or_else(|| format!("unknown predicate `{name}`"))?
                    .clone();
                if arguments.len() != definition.parameters().len() {
                    return Err(format!(
                        "predicate `{}` expects {} argument(s), got {}",
                        definition.name(),
                        definition.parameters().len(),
                        arguments.len()
                    ));
                }
                let definition =
                    self.instantiate_predicate_for_call(&definition, arguments, environment)?;
                if definition
                    .parameters()
                    .iter()
                    .any(|parameter| matches!(parameter.click_type(), ClickType::Algebraic(_)))
                {
                    let mut predicate_environment = SpecElaborationContext::with_current_memory(
                        environment.current_memory.clone(),
                    );
                    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
                        match parameter.click_type() {
                            ClickType::Parameter(name) => {
                                return Err(format!(
                                    "predicate `{}` has unresolved type parameter `{name}`",
                                    definition.name()
                                ));
                            }
                            ClickType::Algebraic(_) => {
                                predicate_environment.algebraic_values.insert(
                                    parameter.name().to_string(),
                                    self.lower_contract_algebraic_to_spec(argument, environment)?,
                                );
                            }
                            ClickType::C(_) if parameter_is_click_array_ref(parameter) => {
                                predicate_environment.array_refs.insert(
                                    parameter.name().to_string(),
                                    self.lower_array_ref_to_spec(argument, environment)?,
                                );
                            }
                            ClickType::C(_) => {
                                predicate_environment.values.insert(
                                    parameter.name().to_string(),
                                    self.lower_contract_expression_to_spec(argument, environment)?,
                                );
                            }
                            ClickType::Integer => {
                                return Err(format!(
                                    "predicate `{}` has an unsupported Integer parameter",
                                    definition.name()
                                ));
                            }
                        }
                    }
                    return self.click_proposition_to_spec_proposition(
                        definition.body(),
                        &predicate_environment,
                    );
                }
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
                    name: definition.name().to_string(),
                    arguments: lowered_arguments,
                })
            }
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    #[inline(never)]
    fn lower_atomic_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => {
                if *operator == ComparisonOperator::In {
                    return Ok(SpecProposition::SequenceMembership {
                        element: self.lower_contract_expression_to_spec(left, environment)?,
                        sequence: self.lower_contract_sequence_to_spec(right, environment)?,
                    });
                }
                let left_is_integer = self.contract_expression_is_integer(left, environment);
                let right_is_integer = self.contract_expression_is_integer(right, environment);
                let left_is_integer = left_is_integer
                    || (right_is_integer
                        && matches!(left, ContractExpression::AlgebraicMatch { .. }));
                let right_is_integer = right_is_integer
                    || (left_is_integer
                        && matches!(right, ContractExpression::AlgebraicMatch { .. }));
                if left_is_integer || right_is_integer {
                    if left_is_integer != right_is_integer
                        && !(if left_is_integer {
                            is_unsuffixed_integer_literal_expression(right)
                        } else {
                            is_unsuffixed_integer_literal_expression(left)
                        })
                    {
                        return Err(
                            "mathematical Integer expressions cannot be compared with C values"
                                .to_string(),
                        );
                    }
                    return Ok(SpecProposition::IntegerComparison {
                        left: self.lower_contract_integer_to_spec(left, environment)?,
                        operator: integer_comparison_operator(*operator)?,
                        right: self.lower_contract_integer_to_spec(right, environment)?,
                    });
                }
                let has_algebraic = contract_expression_is_algebraic(
                    left,
                    self.click_function_environment,
                    environment,
                    &mut Vec::new(),
                ) || contract_expression_is_algebraic(
                    right,
                    self.click_function_environment,
                    environment,
                    &mut Vec::new(),
                );
                if has_algebraic {
                    let equal = match operator {
                        ComparisonOperator::Equal => true,
                        ComparisonOperator::NotEqual => false,
                        _ => {
                            return Err("algebraic values support only `==` and `!=` comparisons"
                                .to_string());
                        }
                    };
                    return Ok(SpecProposition::AlgebraicComparison {
                        left: self.lower_contract_algebraic_to_spec(left, environment)?,
                        equal,
                        right: self.lower_contract_algebraic_to_spec(right, environment)?,
                    });
                }
                let has_sequence =
                    contract_expression_is_sequence(left) || contract_expression_is_sequence(right);
                if has_sequence {
                    let equal = match operator {
                        ComparisonOperator::Equal => true,
                        ComparisonOperator::NotEqual => false,
                        _ => {
                            return Err(
                                "sequences support only `==` and `!=` comparisons".to_string()
                            );
                        }
                    };
                    Ok(SpecProposition::SequenceComparison {
                        left: self.lower_contract_sequence_to_spec(left, environment)?,
                        equal,
                        right: self.lower_contract_sequence_to_spec(right, environment)?,
                    })
                } else {
                    Ok(SpecProposition::Comparison {
                        left: self.lower_contract_expression_to_spec(left, environment)?,
                        operator: c_comparison_operator(*operator),
                        right: self.lower_contract_expression_to_spec(right, environment)?,
                    })
                }
            }
            ClickProposition::FloatClassification {
                expression,
                classification,
            } => Ok(SpecProposition::FloatClassification {
                expression: self.lower_contract_expression_to_spec(expression, environment)?,
                classification: match classification {
                    syntax::C0FloatClassification::Finite => CFloatClassification::Finite,
                    syntax::C0FloatClassification::Infinite => CFloatClassification::Infinite,
                    syntax::C0FloatClassification::Zero => CFloatClassification::Zero,
                    syntax::C0FloatClassification::Subnormal => CFloatClassification::Subnormal,
                    syntax::C0FloatClassification::Nan => CFloatClassification::Nan,
                },
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
            _ => unreachable!("non-atomic proposition dispatched to leaf lowering"),
        }
    }

    fn fixed_resource_field(
        &self,
        access: &ResourceFieldAccess,
        environment: &SpecElaborationContext,
    ) -> Result<Option<AlgebraicValue>, String> {
        let snapshot = environment.snapshot_state.as_ref().or_else(|| {
            (environment.at_function_entry && !environment.function_contract)
                .then_some(self.entry_state)
        });
        snapshot
            .map(|state| {
                state
                    .resource_instance_at_path(access.identity, &access.children)
                    .and_then(|instance| instance.fields().get(access.field_index))
                    .cloned()
                    .ok_or_else(|| {
                        format!(
                            "resource instance `{}` is not owned at this snapshot",
                            access.owner
                        )
                    })
            })
            .transpose()
    }

    fn contract_expression_is_integer(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> bool {
        match expression {
            ContractExpression::ResourceField(access) => {
                matches!(access.click_type, Some(ClickType::Integer))
            }
            ContractExpression::IntegerLiteral(_) => false,
            ContractExpression::Binding(name) => environment.integer_values.contains_key(name),
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.contract_expression_is_integer(inner, environment),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                self.contract_expression_is_integer(left, environment)
                    || self.contract_expression_is_integer(right, environment)
            }
            ContractExpression::Let {
                click_type: Some(ClickType::Integer),
                ..
            } => true,
            ContractExpression::Call { name, .. } if name == "to_integer" => true,
            ContractExpression::Call { name, .. } => self
                .click_function_environment
                .get(name)
                .is_some_and(|function| function.return_type() == &ClickType::Integer),
            _ => false,
        }
    }

    fn lower_contract_integer_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<crate::kernel::SpecIntegerExpression, String> {
        use crate::kernel::SpecIntegerExpression;
        check_integer_lowering_work(1)?;
        match expression {
            ContractExpression::Old(inner) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                return self.lower_contract_integer_to_spec(inner, &old_environment);
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                let snapshot = self
                    .snapshot_environment(selector, environment)
                    .ok_or_else(|| "Integer values require a recorded program point".to_string())?;
                return self.lower_contract_integer_to_spec(expression, &snapshot);
            }
            _ => {}
        }
        if let ContractExpression::ResourceField(access) = expression {
            if access.click_type != Some(ClickType::Integer) {
                return Err("expected an Integer resource field".into());
            }
            if let Some(value) = self.fixed_resource_field(access, environment)? {
                let AlgebraicValue::Integer(value) = value else {
                    return Err("resource field type mismatch".into());
                };
                return Ok(crate::kernel::SpecIntegerExpression::Term(value));
            }
            return Ok(crate::kernel::SpecIntegerExpression::ResourceField(
                crate::kernel::ResourceFieldProjection {
                    identity: access.identity,
                    children: access.children.clone(),
                    field_index: access.field_index,
                    at_entry: environment.at_function_entry,
                },
            ));
        }
        if let ContractExpression::AlgebraicMatch { scrutinee, arms } = expression {
            let scrutinee = self.lower_contract_algebraic_to_spec(scrutinee, environment)?;
            if let crate::kernel::SpecAlgebraicExpressionNode::Constructor { variant, fields } =
                &scrutinee.node
            {
                let arm = arms
                    .iter()
                    .find(|arm| arm.variant == *variant)
                    .ok_or_else(|| format!("missing match arm for `{variant}`"))?;
                if arm.bindings.len() != fields.len() {
                    return Err("datatype match field count mismatch".into());
                }
                let mut body_environment = environment.clone();
                for (name, field) in arm.bindings.iter().zip(fields) {
                    body_environment.integer_values.remove(name);
                    body_environment.values.remove(name);
                    body_environment.algebraic_values.remove(name);
                    body_environment.array_refs.remove(name);
                    match field {
                        crate::kernel::SpecAlgebraicValue::Integer(value) => {
                            body_environment
                                .integer_values
                                .insert(name.clone(), value.clone());
                        }
                        crate::kernel::SpecAlgebraicValue::C(value) => {
                            body_environment.values.insert(name.clone(), value.clone());
                        }
                        crate::kernel::SpecAlgebraicValue::Algebraic(value) => {
                            body_environment
                                .algebraic_values
                                .insert(name.clone(), value.clone());
                        }
                    }
                }
                return self.lower_contract_integer_to_spec(&arm.body, &body_environment);
            }
            return Err("symbolic Integer-valued datatype matches are not supported yet".into());
        }
        match expression {
            ContractExpression::Call { name, arguments } if name != "to_integer" => {
                let definition = self
                    .click_function_environment
                    .get(name)
                    .ok_or_else(|| format!("unknown function `{name}`"))?
                    .clone();
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, environment)?;
                if definition.return_type() != &ClickType::Integer {
                    return Err(format!(
                        "function `{name}` does not return an Integer value"
                    ));
                }
                let arguments = self.lower_click_function_arguments_to_spec(
                    &definition,
                    arguments,
                    environment,
                )?;
                if let Some(arguments) = arguments
                    .iter()
                    .map(spec_argument_to_pure_term)
                    .collect::<Option<Vec<_>>>()
                {
                    return Ok(SpecIntegerExpression::Term(
                        crate::kernel::IntegerTerm::PureFunctionApplication(
                            crate::kernel::SharedIntegerApplication::intern(
                                definition.name().to_string(),
                                arguments,
                            ),
                        ),
                    ));
                }
                Ok(SpecIntegerExpression::PureFunctionApplication {
                    name: definition.name().to_string(),
                    arguments,
                })
            }
            ContractExpression::Binding(name) => {
                let value = environment
                    .integer_values
                    .get(name)
                    .ok_or_else(|| format!("`{name}` is not an Integer binding"))?;
                if let SpecIntegerExpression::Term(term) = value {
                    check_integer_lowering_work(integer_root_work(term))?;
                }
                Ok(value.clone())
            }
            ContractExpression::Call { name, arguments } if name == "to_integer" => {
                let argument = integer_conversion_argument(name, arguments)?;
                if let Ok(nat) = self.lower_contract_algebraic_to_spec(argument, environment) {
                    if nat.algebraic_type.name == "Nat" {
                        return Ok(SpecIntegerExpression::PureFunctionApplication {
                            name: "nat_to_integer".to_string(),
                            arguments: vec![crate::kernel::SpecPureFunctionArgument::Algebraic(
                                nat,
                            )],
                        });
                    }
                }
                let argument = self.lower_contract_expression_to_spec(argument, environment)?;
                if let SpecExpression::Value(value) = &argument {
                    let destination = crate::kernel::MachineIntegerType::from_c_type(
                        value.c_type(),
                    )
                    .ok_or_else(|| {
                        "to_integer expects a signed or unsigned machine integer".to_string()
                    })?;
                    let (CValue::Int16(bits)
                    | CValue::Int32(bits)
                    | CValue::UInt8(bits)
                    | CValue::UInt16(bits)
                    | CValue::UInt32(bits)
                    | CValue::Int64(bits)
                    | CValue::UInt64(bits)) = value
                    else {
                        return Err(
                            "to_integer expects a signed or unsigned machine integer".into()
                        );
                    };
                    // An already evaluated value carries no evaluation effects.
                    // Keep its observation in the shared Integer DAG so aliases
                    // do not duplicate a deferred conversion tree.
                    return crate::kernel::IntegerTerm::from_machine(destination, bits.clone())
                        .map(SpecIntegerExpression::Term)
                        .ok_or_else(|| "invalid machine integer representation".to_string());
                }
                Ok(SpecIntegerExpression::FromMachine(Box::new(argument)))
            }
            ContractExpression::Negate(inner) => {
                let inner = self.lower_contract_integer_to_spec(inner, environment)?;
                match inner {
                    SpecIntegerExpression::Term(term) => {
                        check_integer_lowering_work(integer_root_work(&term))?;
                        Ok(SpecIntegerExpression::Term(
                            crate::kernel::IntegerTerm::negate(term),
                        ))
                    }
                    inner => Ok(SpecIntegerExpression::Negate(Box::new(inner))),
                }
            }
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                let left = self.lower_contract_integer_to_spec(left, environment)?;
                let right = self.lower_contract_integer_to_spec(right, environment)?;
                let operation = match expression {
                    ContractExpression::Add(..) => IntegerOperation::Add,
                    ContractExpression::Subtract(..) => IntegerOperation::Subtract,
                    _ => IntegerOperation::Multiply,
                };
                match (&left, &right) {
                    (SpecIntegerExpression::Term(_), SpecIntegerExpression::Term(_)) => {
                        lower_integer_operation(left, right, operation)
                    }
                    _ => Ok(match operation {
                        IntegerOperation::Add => {
                            SpecIntegerExpression::Add(Box::new(left), Box::new(right))
                        }
                        IntegerOperation::Subtract => {
                            SpecIntegerExpression::Subtract(Box::new(left), Box::new(right))
                        }
                        IntegerOperation::Multiply => {
                            SpecIntegerExpression::Multiply(Box::new(left), Box::new(right))
                        }
                    }),
                }
            }
            ContractExpression::Let {
                name,
                click_type: Some(ClickType::Integer),
                value,
                body,
            } => {
                let value = self.lower_contract_integer_to_spec(value, environment)?;
                let mut body_environment = environment.clone();
                body_environment.values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                body_environment.integer_values.insert(name.clone(), value);
                self.lower_contract_integer_to_spec(body, &body_environment)
            }
            _ => lower_contract_integer_to_spec(expression, &environment.integer_values),
        }
    }

    fn lower_contract_expression_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            ContractExpression::Call { name, arguments }
                if integer_conversion_target(name).is_some() =>
            {
                let argument = integer_conversion_argument(name, arguments)?;
                let destination = crate::kernel::MachineIntegerType::from_c_type(
                    integer_conversion_target(name).unwrap().to_kernel_type(),
                )
                .expect("conversion target is an integral machine type");
                Ok(SpecExpression::IntegerToMachine {
                    value: Box::new(self.lower_contract_integer_to_spec(argument, environment)?),
                    destination,
                })
            }
            ContractExpression::IntegerLiteral(value) => {
                let value = value.parse::<u64>().map_err(|_| {
                    "an arbitrary Integer literal requires Integer context".to_string()
                })?;
                let value = if value <= i32::MAX as u64 {
                    CValue::Int32(Bitvector32Term::Constant(value as u32))
                } else if value <= i64::MAX as u64 {
                    CValue::Int64(Bitvector32Term::Int64Constant(value as i64))
                } else {
                    CValue::UInt64(Bitvector32Term::UInt64Constant(value))
                };
                Ok(SpecExpression::Value(value))
            }
            ContractExpression::ResourceField(access) => {
                let Some(ClickType::C(c_type)) = &access.click_type else {
                    return Err("expected a scalar resource field".into());
                };
                if let Some(value) = self.fixed_resource_field(access, environment)? {
                    let AlgebraicValue::C(value) = value else {
                        return Err("resource field type mismatch".into());
                    };
                    return Ok(SpecExpression::Value(value));
                }
                Ok(SpecExpression::ResourceField {
                    projection: crate::kernel::ResourceFieldProjection {
                        identity: access.identity,
                        children: access.children.clone(),
                        field_index: access.field_index,
                        at_entry: environment.at_function_entry,
                    },
                    c_type: c_type.to_kernel_type(),
                })
            }
            ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => {
                Err("a sequence value is only valid as an operand of `==` or `!=`".to_string())
            }
            ContractExpression::AlgebraicConstructor { .. }
            | ContractExpression::AlgebraicVariable { .. } => Err(
                "an algebraic value is valid only as a comparison operand or match scrutinee"
                    .to_string(),
            ),
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                let scrutinee = self.lower_contract_algebraic_to_spec(scrutinee, environment)?;
                if let SpecAlgebraicExpressionNode::Constructor { variant, fields } =
                    &scrutinee.node
                {
                    let arm = arms
                        .iter()
                        .find(|arm| arm.variant == *variant)
                        .ok_or_else(|| format!("missing match arm for `{variant}`"))?;
                    let mut body_environment = environment.clone();
                    for (binding, field) in arm.bindings.iter().zip(fields.iter()) {
                        match field {
                            SpecAlgebraicValue::C(field) => {
                                body_environment.integer_values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                                body_environment
                                    .values
                                    .insert(binding.clone(), field.clone());
                            }
                            SpecAlgebraicValue::Algebraic(field) => {
                                body_environment.values.remove(binding);
                                body_environment.integer_values.remove(binding);
                                body_environment
                                    .algebraic_values
                                    .insert(binding.clone(), field.clone());
                            }
                            SpecAlgebraicValue::Integer(field) => {
                                body_environment.values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                                body_environment
                                    .integer_values
                                    .insert(binding.clone(), field.clone());
                            }
                        }
                    }
                    return self.lower_contract_expression_to_spec(&arm.body, &body_environment);
                }
                let lowered_arms = arms
                    .iter()
                    .map(|arm| {
                        let variant = scrutinee
                            .algebraic_type
                            .variants
                            .iter()
                            .find(|variant| variant.name == arm.variant)
                            .ok_or_else(|| format!("unknown match variant `{}`", arm.variant))?;
                        let mut body_environment = environment.clone();
                        for (binding, binding_type) in arm.bindings.iter().zip(&variant.fields) {
                            match binding_type {
                                AlgebraicValueType::C(_) => {
                                    body_environment.values.remove(binding);
                                    body_environment.algebraic_values.remove(binding);
                                }
                                AlgebraicValueType::Algebraic { .. }
                                | AlgebraicValueType::Parameter(_) => {
                                    body_environment.values.remove(binding);
                                    body_environment.algebraic_values.insert(
                                        binding.clone(),
                                        SpecAlgebraicExpression {
                                            algebraic_type: self
                                                .cached_algebraic_kernel_type_from_value_type(
                                                    binding_type,
                                                )?,
                                            node: SpecAlgebraicExpressionNode::Binding(
                                                binding.clone(),
                                            ),
                                        },
                                    );
                                }
                                AlgebraicValueType::Integer => {
                                    body_environment.values.remove(binding);
                                    body_environment.algebraic_values.remove(binding);
                                    let variable =
                                        crate::kernel::Variable(self.next_quantifier_variable);
                                    self.next_quantifier_variable += 1;
                                    body_environment.integer_values.insert(
                                        binding.clone(),
                                        crate::kernel::SpecIntegerExpression::Term(
                                            crate::kernel::IntegerTerm::var(variable),
                                        ),
                                    );
                                }
                            }
                        }
                        Ok(crate::kernel::SpecAlgebraicMatchArm {
                            variant: arm.variant.clone(),
                            bindings: arm.bindings.clone(),
                            binding_types: variant.fields.clone(),
                            body: self
                                .lower_contract_expression_to_spec(&arm.body, &body_environment)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(SpecExpression::AlgebraicMatch {
                    scrutinee: Box::new(scrutinee),
                    arms: lowered_arms,
                })
            }
            ContractExpression::QualifiedC {
                lowered: expression,
                ..
            }
            | ContractExpression::CFragment(expression)
            | ContractExpression::Field {
                lowered: expression,
                ..
            } => self.lower_c_fragment_to_spec(expression, environment),
            ContractExpression::Binding(name) => {
                if environment.algebraic_values.contains_key(name) {
                    return Err(format!(
                        "algebraic binding `{name}` is not valid in a C-valued expression"
                    ));
                }
                self.lower_c_fragment_to_spec(&CExpression::Variable(name.clone()), environment)
            }
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
                            Some(SpecExpression::Value(value)) => {
                                Some(Some(AlgebraicValue::C(value.clone())))
                            }
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
            ContractExpression::Negate(expression) => {
                if self.contract_expression_is_integer(expression, environment) {
                    return Err(
                        "an Integer expression must be lowered as a comparison operand".to_string(),
                    );
                }
                if let ContractExpression::IntegerLiteral(value) = expression.as_ref()
                    && let Ok(value) = value.parse::<u64>()
                    && value <= (i32::MAX as u64) + 1
                {
                    return Ok(SpecExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant(0u32.wrapping_sub(value as u32)),
                    )));
                }
                Ok(SpecExpression::Subtract(
                    Box::new(SpecExpression::Value(int32(0))),
                    Box::new(self.lower_contract_expression_to_spec(expression, environment)?),
                ))
            }
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
                click_type,
                value,
                body,
            } => {
                let value_is_algebraic = contract_expression_is_algebraic(
                    value,
                    self.click_function_environment,
                    environment,
                    &mut Vec::new(),
                );
                if value_is_algebraic {
                    let value = self.lower_contract_algebraic_to_spec(value, environment)?;
                    if let Some(ClickType::Algebraic(expected)) = click_type
                        && value.algebraic_type != self.cached_algebraic_kernel_type(expected)?
                    {
                        return Err(format!(
                            "let binding `{name}` has an algebraic value of the wrong type"
                        ));
                    }
                    let mut body_environment = environment.clone();
                    body_environment
                        .algebraic_values
                        .insert(name.clone(), value);
                    return self.lower_contract_expression_to_spec(body, &body_environment);
                }
                if matches!(click_type, Some(ClickType::Integer))
                    || self.contract_expression_is_integer(value, environment)
                {
                    return Err(
                        "an Integer let expression must be lowered as a comparison operand"
                            .to_string(),
                    );
                }
                let value = self.lower_contract_expression_to_spec(value, environment)?;
                if let (Some(ClickType::C(c_type)), SpecExpression::Value(fixed)) =
                    (click_type, &value)
                    && !c_value_matches_click_type(fixed, *c_type)
                {
                    return Err(format!(
                        "let binding `{name}` evaluated to {fixed:?}, which does not match {c_type:?}"
                    ));
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

    fn lower_contract_algebraic_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecAlgebraicExpression, String> {
        match expression {
            ContractExpression::ResourceField(access) => {
                let Some(ClickType::Algebraic(ty)) = &access.click_type else {
                    return Err("expected an algebraic resource field".into());
                };
                let algebraic_type = self.cached_algebraic_kernel_type(ty)?;
                let node = if let Some(value) = self.fixed_resource_field(access, environment)? {
                    let AlgebraicValue::Algebraic(AlgebraicTerm {
                        node: AlgebraicTermNode::Variable(variable),
                        ..
                    }) = value
                    else {
                        return Err("only entry-bound symbolic resource fields support fixed snapshots in this slice".into());
                    };
                    SpecAlgebraicExpressionNode::Variable(variable)
                } else {
                    SpecAlgebraicExpressionNode::ResourceField(
                        crate::kernel::ResourceFieldProjection {
                            identity: access.identity,
                            children: access.children.clone(),
                            field_index: access.field_index,
                            at_entry: environment.at_function_entry,
                        },
                    )
                };
                Ok(SpecAlgebraicExpression {
                    algebraic_type,
                    node,
                })
            }
            ContractExpression::AlgebraicVariable {
                name,
                algebraic_type,
                binder_index,
            } => {
                if let Some(value) = environment.algebraic_values.get(name) {
                    return Ok(value.clone());
                }
                self.symbolic_algebraic_variable(name, algebraic_type, *binder_index)
            }
            ContractExpression::Binding(name) => environment
                .algebraic_values
                .get(name)
                .cloned()
                .ok_or_else(|| format!("`{name}` is not an algebraic binding in this scope")),
            ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            } => {
                let algebraic_type = self.cached_algebraic_kernel_type(algebraic_type)?;
                let schema = algebraic_type
                    .variants
                    .iter()
                    .find(|schema| schema.name == *variant)
                    .ok_or_else(|| format!("unknown match variant `{variant}`"))?;
                if arguments.len() != schema.fields.len() {
                    return Err(format!(
                        "constructor `{variant}` expects {} argument(s), got {}",
                        schema.fields.len(),
                        arguments.len(),
                    ));
                }
                let fields = arguments
                    .iter()
                    .zip(&schema.fields)
                    .map(|(argument, field_type)| match field_type {
                        AlgebraicValueType::C(_) => self
                            .lower_contract_expression_to_spec(argument, environment)
                            .map(SpecAlgebraicValue::C),
                        AlgebraicValueType::Integer => self
                            .lower_contract_integer_to_spec(argument, environment)
                            .map(SpecAlgebraicValue::Integer),
                        AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_) => {
                            self.lower_contract_algebraic_to_spec(argument, environment)
                                .map(SpecAlgebraicValue::Algebraic)
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(SpecAlgebraicExpression {
                    algebraic_type,
                    node: SpecAlgebraicExpressionNode::Constructor {
                        variant: variant.clone(),
                        fields,
                    },
                })
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                let scrutinee = self.lower_contract_algebraic_to_spec(scrutinee, environment)?;
                if let SpecAlgebraicExpressionNode::Constructor { variant, fields } =
                    &scrutinee.node
                {
                    let arm = arms
                        .iter()
                        .find(|arm| arm.variant == *variant)
                        .ok_or_else(|| format!("missing match arm for `{variant}`"))?;
                    let mut body_environment = environment.clone();
                    for (binding, field) in arm.bindings.iter().zip(fields.iter()) {
                        match field {
                            SpecAlgebraicValue::C(field) => {
                                body_environment.integer_values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                                body_environment
                                    .values
                                    .insert(binding.clone(), field.clone());
                            }
                            SpecAlgebraicValue::Algebraic(field) => {
                                body_environment.values.remove(binding);
                                body_environment.integer_values.remove(binding);
                                body_environment
                                    .algebraic_values
                                    .insert(binding.clone(), field.clone());
                            }
                            SpecAlgebraicValue::Integer(field) => {
                                body_environment.values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                                body_environment
                                    .integer_values
                                    .insert(binding.clone(), field.clone());
                            }
                        }
                    }
                    return self.lower_contract_algebraic_to_spec(&arm.body, &body_environment);
                }
                let mut lowered_arms = Vec::new();
                let mut result_type = None;
                for arm in arms {
                    let variant = scrutinee
                        .algebraic_type
                        .variants
                        .iter()
                        .find(|variant| variant.name == arm.variant)
                        .ok_or_else(|| format!("unknown match variant `{}`", arm.variant))?;
                    let mut body_environment = environment.clone();
                    for (binding, binding_type) in arm.bindings.iter().zip(&variant.fields) {
                        match binding_type {
                            AlgebraicValueType::C(_) => {
                                body_environment.values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                            }
                            AlgebraicValueType::Algebraic { .. }
                            | AlgebraicValueType::Parameter(_) => {
                                body_environment.values.remove(binding);
                                body_environment.algebraic_values.insert(
                                    binding.clone(),
                                    SpecAlgebraicExpression {
                                        algebraic_type: self
                                            .cached_algebraic_kernel_type_from_value_type(
                                                binding_type,
                                            )?,
                                        node: SpecAlgebraicExpressionNode::Binding(binding.clone()),
                                    },
                                );
                            }
                            AlgebraicValueType::Integer => {
                                body_environment.values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                                let variable =
                                    crate::kernel::Variable(self.next_quantifier_variable);
                                self.next_quantifier_variable += 1;
                                body_environment.integer_values.insert(
                                    binding.clone(),
                                    crate::kernel::SpecIntegerExpression::Term(
                                        crate::kernel::IntegerTerm::var(variable),
                                    ),
                                );
                            }
                        }
                    }
                    let body =
                        self.lower_contract_algebraic_to_spec(&arm.body, &body_environment)?;
                    result_type.get_or_insert_with(|| body.algebraic_type.clone());
                    lowered_arms.push(SpecAlgebraicResultMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: variant.fields.clone(),
                        body: Box::new(body),
                    });
                }
                Ok(SpecAlgebraicExpression {
                    algebraic_type: result_type
                        .ok_or_else(|| "an algebraic match must have an arm".to_string())?,
                    node: SpecAlgebraicExpressionNode::Match {
                        scrutinee: Box::new(scrutinee),
                        arms: lowered_arms,
                    },
                })
            }
            ContractExpression::Old(inner) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_algebraic_to_spec(inner, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                let snapshot = self.snapshot_environment(selector, environment).ok_or_else(|| {
                    "algebraic values at unresolved program points are not supported in this slice"
                        .to_string()
                })?;
                self.lower_contract_algebraic_to_spec(expression, &snapshot)
            }
            ContractExpression::Let {
                name, value, body, ..
            } => {
                let value = self.lower_contract_algebraic_to_spec(value, environment)?;
                let mut body_environment = environment.clone();
                body_environment
                    .algebraic_values
                    .insert(name.clone(), value);
                self.lower_contract_algebraic_to_spec(body, &body_environment)
            }
            ContractExpression::Call { name, arguments } => {
                if name == "to_nat" {
                    let argument = integer_conversion_argument(name, arguments)?;
                    let value = self.lower_contract_integer_to_spec(argument, environment)?;
                    let algebraic_type = self
                        .cached_algebraic_kernel_type(&AlgebraicTypeApplication::concrete("Nat"))?;
                    return Ok(SpecAlgebraicExpression {
                        algebraic_type,
                        node: SpecAlgebraicExpressionNode::PureFunctionApplication {
                            name: "to_nat".to_string(),
                            arguments: vec![crate::kernel::SpecPureFunctionArgument::Integer(
                                value,
                            )],
                        },
                    });
                }
                self.lower_click_function_call_to_algebraic_spec(name, arguments, environment)
            }
            _ => Err("expected an algebraic value".to_string()),
        }
    }

    fn symbolic_algebraic_variable(
        &mut self,
        name: &str,
        algebraic_type: &AlgebraicTypeApplication,
        binder_index: usize,
    ) -> Result<SpecAlgebraicExpression, String> {
        if let Some(value) = self.algebraic_variables.get(name) {
            return Ok(value.clone());
        }
        const ALGEBRAIC_VARIABLE_BASE: u64 = 4_000_000;
        const ALGEBRAIC_BINDER_STRIDE: u64 = 65_536;
        let binder_base = ALGEBRAIC_VARIABLE_BASE
            .checked_add((binder_index as u64).saturating_mul(ALGEBRAIC_BINDER_STRIDE))
            .ok_or_else(|| "too many algebraic binders".to_string())?;
        let value = SpecAlgebraicExpression {
            algebraic_type: self.cached_algebraic_kernel_type(algebraic_type)?,
            node: SpecAlgebraicExpressionNode::Variable(Variable(binder_base)),
        };
        self.algebraic_variables
            .insert(name.to_string(), value.clone());
        Ok(value)
    }

    fn cached_algebraic_kernel_type(
        &mut self,
        application: &AlgebraicTypeApplication,
    ) -> Result<AlgebraicType, String> {
        if application.rigid {
            return Ok(AlgebraicType::parameter(application.name.clone()));
        }
        let arguments = algebraic_kernel_type_arguments(application)?;
        let key = (application.name.clone(), arguments);
        if let Some(algebraic_type) = self.algebraic_types.get(&key) {
            return Ok(algebraic_type.clone());
        }
        let algebraic_type = algebraic_kernel_type(self.click_function_environment, application)?;
        self.algebraic_types.insert(key, algebraic_type.clone());
        Ok(algebraic_type)
    }

    fn cached_algebraic_kernel_type_from_value_type(
        &mut self,
        value_type: &AlgebraicValueType,
    ) -> Result<AlgebraicType, String> {
        if let AlgebraicValueType::Parameter(name) = value_type {
            return Ok(AlgebraicType::parameter(name.clone()));
        }
        let AlgebraicValueType::Algebraic { name, arguments } = value_type else {
            return Err("expected an algebraic value type".to_string());
        };
        let key = (name.clone(), arguments.clone());
        if let Some(algebraic_type) = self.algebraic_types.get(&key) {
            return Ok(algebraic_type.clone());
        }
        let algebraic_type =
            algebraic_kernel_type_from_parts(self.click_function_environment, name, arguments)?;
        self.algebraic_types.insert(key, algebraic_type.clone());
        Ok(algebraic_type)
    }

    fn lower_click_function_call_to_algebraic_spec(
        &mut self,
        name: &str,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<SpecAlgebraicExpression, String> {
        let definition = self
            .click_function_environment
            .get(name)
            .ok_or_else(|| format!("unknown function `{name}`"))?
            .clone();
        let definition =
            self.instantiate_click_function_for_call(&definition, arguments, environment)?;
        let ClickType::Algebraic(result_type) = definition.return_type() else {
            return Err(format!(
                "function `{name}` does not return an algebraic value"
            ));
        };
        if arguments.len() != definition.parameters().len() {
            return Err(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                arguments.len()
            ));
        }
        Ok(SpecAlgebraicExpression {
            algebraic_type: self.cached_algebraic_kernel_type(result_type)?,
            node: SpecAlgebraicExpressionNode::PureFunctionApplication {
                name: definition.name().to_string(),
                arguments: self.lower_click_function_arguments_to_spec(
                    &definition,
                    arguments,
                    environment,
                )?,
            },
        })
    }

    fn lower_click_function_arguments_to_spec(
        &mut self,
        definition: &ClickFunctionDefinition,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<Vec<crate::kernel::SpecPureFunctionArgument>, String> {
        definition
            .parameters()
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| match parameter.click_type() {
                ClickType::Parameter(name) => Err(format!(
                    "function `{}` has unresolved type parameter `{name}`",
                    definition.name()
                )),
                ClickType::Integer => self
                    .lower_contract_integer_to_spec(argument, environment)
                    .map(crate::kernel::SpecPureFunctionArgument::Integer),
                ClickType::Algebraic(_) => self
                    .lower_contract_algebraic_to_spec(argument, environment)
                    .map(crate::kernel::SpecPureFunctionArgument::Algebraic),
                ClickType::C(_) if parameter_is_click_array_ref(parameter) => {
                    let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                    Ok(crate::kernel::SpecPureFunctionArgument::ArrayRef {
                        memory: array_ref.memory,
                        pointer: array_ref.pointer,
                        element_type: array_ref.element_type,
                    })
                }
                ClickType::C(_) => self
                    .lower_contract_expression_to_spec(argument, environment)
                    .map(crate::kernel::SpecPureFunctionArgument::Value),
            })
            .collect()
    }

    fn instantiate_click_function_for_call(
        &mut self,
        definition: &ClickFunctionDefinition,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<ClickFunctionDefinition, String> {
        if definition.type_parameters().is_empty() {
            return Ok(definition.clone());
        }
        let argument_types = definition
            .parameters()
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| {
                self.infer_call_argument_type(parameter.click_type(), argument, environment)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let substitution = generics::infer_type_substitution(
            "function",
            definition.name(),
            definition.type_parameters(),
            definition
                .parameters()
                .iter()
                .map(|parameter| parameter.click_type().clone()),
            argument_types,
        )?;
        generics::instantiate_function(definition, &substitution)
    }

    fn instantiate_predicate_for_call(
        &mut self,
        definition: &PredicateDefinition,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<PredicateDefinition, String> {
        if definition.type_parameters().is_empty() {
            return Ok(definition.clone());
        }
        let argument_types = definition
            .parameters()
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| {
                self.infer_call_argument_type(parameter.click_type(), argument, environment)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let substitution = generics::infer_type_substitution(
            "predicate",
            definition.name(),
            definition.type_parameters(),
            definition
                .parameters()
                .iter()
                .map(|parameter| parameter.click_type().clone()),
            argument_types,
        )?;
        generics::instantiate_predicate(definition, &substitution)
    }

    fn infer_call_argument_type(
        &mut self,
        expected: &ClickType,
        argument: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<Option<ClickType>, String> {
        match expected {
            ClickType::Algebraic(_) => {
                let value = self.lower_contract_algebraic_to_spec(argument, environment)?;
                Ok(Some(generics::click_type_from_algebraic_value_type(
                    &value.algebraic_type.value_type(),
                )))
            }
            ClickType::C(c_type) => Ok(Some(ClickType::C(*c_type))),
            ClickType::Integer => Ok(Some(ClickType::Integer)),
            ClickType::Parameter(_) => {
                self.infer_unconstrained_call_argument_type(argument, environment)
            }
        }
    }

    fn infer_unconstrained_call_argument_type(
        &mut self,
        argument: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<Option<ClickType>, String> {
        match argument {
            ContractExpression::IntegerLiteral(_) | ContractExpression::Negate(_) => {
                Ok(generics::default_numeral_click_type(argument))
            }
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.infer_unconstrained_call_argument_type(inner, environment),
            ContractExpression::ResourceField(access) => Ok(access.click_type.clone()),
            ContractExpression::AlgebraicVariable { algebraic_type, .. }
            | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
                Ok(Some(ClickType::Algebraic(algebraic_type.clone())))
            }
            ContractExpression::Binding(name) => {
                if let Some(value) = environment.algebraic_values.get(name) {
                    return Ok(Some(generics::click_type_from_algebraic_value_type(
                        &value.algebraic_type.value_type(),
                    )));
                }
                Ok(environment
                    .values
                    .get(name)
                    .and_then(spec_expression_click_type))
            }
            ContractExpression::CFragment(CExpression::Value(value)) => Ok(Some(ClickType::C(
                generics::c0_type_from_kernel(value.c_type()),
            ))),
            ContractExpression::CFragment(CExpression::Variable(name)) => Ok(environment
                .values
                .get(name)
                .and_then(spec_expression_click_type)),
            ContractExpression::Call { name, arguments } => {
                let definition = self
                    .click_function_environment
                    .get(name)
                    .ok_or_else(|| format!("unknown function `{name}`"))?
                    .clone();
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, environment)?;
                Ok(Some(definition.return_type().clone()))
            }
            _ => Ok(None),
        }
    }

    fn lower_contract_sequence_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecSequenceExpression, String> {
        match expression {
            ContractExpression::SequenceLiteral(elements) => Ok(SpecSequenceExpression::Literal(
                elements
                    .iter()
                    .map(|element| self.lower_contract_expression_to_spec(element, environment))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            ContractExpression::SequenceConcat(left, right) => Ok(SpecSequenceExpression::Concat(
                Box::new(self.lower_contract_sequence_to_spec(left, environment)?),
                Box::new(self.lower_contract_sequence_to_spec(right, environment)?),
            )),
            ContractExpression::Old(inner) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_sequence_to_spec(inner, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                if let Some(snapshot) = self.snapshot_environment(selector, environment) {
                    return self.lower_contract_sequence_to_spec(expression, &snapshot);
                }
                match self.resolve_visit_selector(selector)? {
                    ResolvedProgramPoint::Current => {
                        self.lower_contract_sequence_to_spec(expression, environment)
                    }
                    ResolvedProgramPoint::FunctionEntry => {
                        let old_environment =
                            environment.old_state(&self.entry_values, self.entry_state.memory())?;
                        self.lower_contract_sequence_to_spec(expression, &old_environment)
                    }
                    ResolvedProgramPoint::LoopEntry(_) => Err(
                        "sequence snapshots at loop entry are not in the first sequence slice"
                            .to_string(),
                    ),
                }
            }
            _ => Err("sequence equality requires a sequence on both sides".to_string()),
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
        let mut array_refs = environment
            .array_refs
            .iter()
            .map(|(name, array_ref)| {
                (
                    name.clone(),
                    SpecArrayRef {
                        memory: SpecMemory::Fixed(state.memory().clone()),
                        pointer: array_ref.pointer.clone(),
                        element_type: array_ref.element_type,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        array_refs.extend(state.locals().array_object_values().map(
            |(name, value, element_type)| {
                (
                    name.to_string(),
                    SpecArrayRef {
                        memory: SpecMemory::Fixed(state.memory().clone()),
                        pointer: SpecExpression::Value(value.clone()),
                        element_type,
                    },
                )
            },
        ));
        Some(SpecElaborationContext {
            values,
            integer_values: environment.integer_values.clone(),
            algebraic_values: environment.algebraic_values.clone(),
            array_refs: array_refs.into_iter().collect(),
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
                    && self
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
            CExpression::Cast {
                expression,
                target_type,
                ..
            } if *target_type == CType::UInt32 || target_type.is_pointer() => {
                Ok(SpecExpression::Cast(
                    Box::new(self.lower_c_fragment_to_spec(expression, environment)?),
                    *target_type,
                ))
            }
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
                ..
            } => self.lower_c_fragment_to_spec(pointer, environment),
            CExpression::TypedLoad {
                pointer,
                value_type,
                ..
            } => Ok(SpecExpression::MemoryLoad {
                memory: environment.current_memory.clone(),
                pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                value_type: *value_type,
            }),
            CExpression::Load(pointer) => Ok(SpecExpression::MemoryLoad {
                memory: environment.current_memory.clone(),
                pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                value_type: self
                    .c_expression_array_element_type(pointer, environment)
                    .unwrap_or(CType::Int32),
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
            .ok_or_else(|| format!("unknown function `{name}`"))?
            .clone();
        let definition =
            self.instantiate_click_function_for_call(&definition, arguments, environment)?;
        if arguments.len() != definition.parameters().len() {
            return Err(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                arguments.len()
            ));
        }

        let ClickType::C(result_type) = definition.return_type() else {
            return Err(format!("function `{name}` does not return a C value"));
        };
        Ok(SpecExpression::PureFunctionApplication {
            name: definition.name().to_string(),
            arguments: self.lower_click_function_arguments_to_spec(
                &definition,
                arguments,
                environment,
            )?,
            result_type: result_type.to_kernel_type(),
        })
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
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
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
            ContractExpression::Binding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .unwrap_or_else(|| {
                    self.array_ref_element_type_for_name_in_environment(name, environment)
                }),
            ContractExpression::QualifiedC { lowered, .. }
            | ContractExpression::Field { lowered, .. } => self
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
            ContractExpression::QualifiedC {
                lowered: expression,
                ..
            }
            | ContractExpression::CFragment(expression)
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
            CExpression::Value(CValue::Pointer(pointer)) => pointer.c_type().pointee_type(),
            CExpression::Cast { target_type, .. } => target_type.pointee_type(),
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

    fn loop_frame_checks(&self, loop_index: usize) -> Result<Vec<CLoopEffectCheck>, ClickError> {
        let mut checks: Vec<CLoopEffectCheck> = Vec::new();
        // A loop body can only write memory the function owns, so a loop with
        // no clause of its own inherits the function's owned write footprint
        // instead of becoming an unconditional havoc. An owned footprint that
        // is empty -- a contract that only `views` memory -- is an inherited
        // empty footprint, not the absence of one: the loop still may not
        // write any of the memory it can reach, so every viewed cell is framed
        // across it. The inherited claim stays checked at every back edge, so
        // a body that does write outside the footprint fails there.
        if let Some(declaration) = self.loop_resources.get(&loop_index) {
            // A loop that declares its own resources has the shape of a
            // callee: its footprint is the memory it owns, not everything the
            // function owns. The claim stays checked at every back edge.
            checks.push(CLoopEffectCheck::new_with_span(
                CLoopEffect::Mutable(declaration.owned_segments.clone()),
                CLoopEffectSpan::Whole,
                Some(format!("loop {loop_index} declared owned resource frame")),
            ));
        } else if self.inherits_resource_derived_frame
            || !self.implicit_contract_mutable_segments.is_empty()
        {
            checks.push(CLoopEffectCheck::new_with_span(
                CLoopEffect::Mutable(self.implicit_contract_mutable_segments.to_vec()),
                CLoopEffectSpan::Whole,
                Some(format!("loop {loop_index} inherited owned resource frame")),
            ));
        }
        Ok(checks)
    }
}

fn spec_expression_click_type(expression: &SpecExpression) -> Option<ClickType> {
    let c_type = match expression {
        SpecExpression::ResourceField { c_type, .. } => *c_type,
        SpecExpression::Value(value) => value.c_type(),
        SpecExpression::PureFunctionApplication { result_type, .. }
        | SpecExpression::MemoryLoad {
            value_type: result_type,
            ..
        } => *result_type,
        SpecExpression::LoopEntrySnapshot(inner) => {
            return spec_expression_click_type(inner);
        }
        SpecExpression::If { then_branch, .. } => {
            return spec_expression_click_type(then_branch);
        }
        SpecExpression::Let { body, .. } => {
            return spec_expression_click_type(body);
        }
        SpecExpression::PointerOffset { .. } => CType::VoidPointer,
        _ => return None,
    };
    Some(ClickType::C(generics::c0_type_from_kernel(c_type)))
}

fn algebraic_kernel_type_arguments(
    application: &AlgebraicTypeApplication,
) -> Result<Vec<AlgebraicValueType>, String> {
    application
        .arguments
        .iter()
        .map(click_type_to_algebraic_value_type)
        .collect()
}

fn click_type_to_algebraic_value_type(
    click_type: &ClickType,
) -> Result<AlgebraicValueType, String> {
    match click_type {
        ClickType::Parameter(name) => Err(format!("unresolved type parameter `{name}`")),
        ClickType::C(c_type) => Ok(AlgebraicValueType::C(c_type.to_kernel_type())),
        ClickType::Integer => Ok(AlgebraicValueType::Integer),
        ClickType::Algebraic(application) if application.rigid => {
            Ok(AlgebraicValueType::Parameter(application.name.clone()))
        }
        ClickType::Algebraic(application) => Ok(AlgebraicValueType::Algebraic {
            name: application.name.clone(),
            arguments: algebraic_kernel_type_arguments(application)?,
        }),
    }
}

fn algebraic_kernel_type(
    environment: &ClickFunctionEnvironment,
    application: &AlgebraicTypeApplication,
) -> Result<AlgebraicType, String> {
    if application.rigid {
        return Ok(AlgebraicType::parameter(application.name.clone()));
    }
    let arguments = algebraic_kernel_type_arguments(application)?;
    algebraic_kernel_type_from_parts(environment, &application.name, &arguments)
}

fn algebraic_kernel_type_from_parts(
    environment: &ClickFunctionEnvironment,
    name: &str,
    arguments: &[AlgebraicValueType],
) -> Result<AlgebraicType, String> {
    let root_type = AlgebraicValueType::Algebraic {
        name: name.to_string(),
        arguments: arguments.to_vec(),
    };
    let mut schemas = BTreeMap::new();
    collect_algebraic_kernel_schemas(environment, &root_type, &mut schemas)?;
    let schemas = std::sync::Arc::new(AlgebraicSchemas::new(schemas));
    let variants = schemas
        .get(&root_type)
        .cloned()
        .ok_or_else(|| format!("missing algebraic datatype schema for `{name}`"))?;
    Ok(AlgebraicType {
        rigid: false,
        name: name.to_string(),
        arguments: arguments.to_vec(),
        variants,
        schemas,
    })
}

fn collect_algebraic_kernel_schemas(
    environment: &ClickFunctionEnvironment,
    value_type: &AlgebraicValueType,
    schemas: &mut BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>,
) -> Result<(), String> {
    if schemas.contains_key(value_type) {
        return Ok(());
    }
    let AlgebraicValueType::Algebraic { name, arguments } = value_type else {
        return Ok(());
    };
    let definition = environment
        .algebraic_type_definitions
        .get(name)
        .ok_or_else(|| format!("unknown algebraic datatype `{name}`"))?;
    let variants = definition
        .variants()
        .iter()
        .map(|variant| {
            Ok(AlgebraicVariantType {
                name: variant.name().to_string(),
                fields: variant
                    .fields()
                    .iter()
                    .map(|field| {
                        instantiate_algebraic_kernel_field_type(definition, arguments, field)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    schemas.insert(value_type.clone(), variants.clone().into());
    for nested in variants
        .iter()
        .flat_map(|variant| variant.fields.iter())
        .filter(|field| matches!(field, AlgebraicValueType::Algebraic { .. }))
    {
        collect_algebraic_kernel_schemas(environment, nested, schemas)?;
    }
    Ok(())
}

fn instantiate_algebraic_kernel_field_type(
    definition: &AlgebraicTypeDefinition,
    arguments: &[AlgebraicValueType],
    field: &AlgebraicFieldType,
) -> Result<AlgebraicValueType, String> {
    match field {
        AlgebraicFieldType::Integer => Ok(AlgebraicValueType::Integer),
        AlgebraicFieldType::C(c_type) => Ok(AlgebraicValueType::C(c_type.to_kernel_type())),
        AlgebraicFieldType::Parameter(name) => definition
            .type_parameters()
            .iter()
            .position(|parameter| parameter == name)
            .and_then(|index| arguments.get(index))
            .cloned()
            .ok_or_else(|| format!("unresolved type parameter `{name}`")),
        AlgebraicFieldType::Algebraic {
            name,
            arguments: nested_arguments,
        } => Ok(AlgebraicValueType::Algebraic {
            name: name.clone(),
            arguments: nested_arguments
                .iter()
                .map(|argument| {
                    instantiate_algebraic_kernel_field_type(definition, arguments, argument)
                })
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}
