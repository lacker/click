use super::*;
use crate::kernel::{AlgebraicTerm, AlgebraicTermNode, CLoopEffectOrigin};

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
    Vec<Option<usize>>,
    Vec<SpecProposition>,
    Vec<CMemorySegment>,
    Vec<CMemorySegment>,
    Vec<CFunctionContractClaim>,
    bool,
    Vec<CPredicateUnfolding>,
);

/// Records each declared memory-independent pure function's body with the
/// kernel, once per verification.
///
/// This is what lets arm refutation ask what a predicate returns at one
/// constructor without a proof script to place an `unfold` in (package A21).
/// The bodies are lowered by the same lowering every other annotation uses,
/// with the parameters left as the names the kernel's evaluation binds: a C
/// parameter reads as a local, an algebraic one as a binding.
///
/// Only whole, concrete declarations take part. A generic declaration, a
/// parameter or result that is not a C or algebraic value, a memory-dependent
/// body, or a body this lowering refuses simply is not recorded, and the
/// refutation rule then has nothing to say about that function.
pub(in crate::surface) fn register_kernel_pure_function_definitions(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
) {
    for definition in click_function_environment.definitions.values() {
        if !definition.type_parameters().is_empty()
            || !click_function_environment.is_memory_independent(definition.name())
            || definition.return_type().c_type().is_none()
        {
            continue;
        }
        if let Some(lowered) = lower_kernel_pure_function_definition(
            definition,
            predicate_environment,
            click_function_environment,
            struct_layouts,
        ) {
            crate::kernel::register_pure_function_definition(lowered);
        }
    }
}

fn lower_kernel_pure_function_definition(
    definition: &ClickFunctionDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Option<crate::kernel::CPureFunctionDefinition> {
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
                    click_array_element_type(parameter.click_type().c_type()?)?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: click_parameter_pointer_element_widths_with_layouts(
            definition.parameters(),
            struct_layouts,
        ),
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
    let mut parameters = Vec::new();
    let mut context = SpecElaborationContext::default();
    for parameter in definition.parameters() {
        match parameter.click_type() {
            ClickType::C(c_type) => {
                parameters.push(crate::kernel::CPureFunctionParameter::c(
                    parameter.name(),
                    c_type.to_kernel_type(),
                ));
            }
            ClickType::Algebraic(application) => {
                let algebraic_type = lowerer.cached_algebraic_kernel_type(application).ok()?;
                context.algebraic_values.insert(
                    parameter.name().to_string(),
                    SpecAlgebraicExpression {
                        algebraic_type: algebraic_type.clone(),
                        node: SpecAlgebraicExpressionNode::Binding(parameter.name().to_string()),
                    },
                );
                parameters.push(crate::kernel::CPureFunctionParameter::algebraic(
                    parameter.name(),
                    algebraic_type,
                ));
            }
            ClickType::Integer | ClickType::Parameter(_) => return None,
        }
    }
    let body = lowerer
        .lower_contract_expression_to_spec(definition.body(), &context)
        .ok()?;
    Some(crate::kernel::CPureFunctionDefinition::new(
        definition.name(),
        parameters,
        body,
    ))
}

pub(in crate::surface) fn lower_composite_resource_condition(
    definition: &ResourceDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
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
        parameter_pointer_element_widths: click_parameter_pointer_element_widths_with_layouts(
            definition.parameters(),
            struct_layouts,
        ),
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
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Result<Vec<SpecProposition>, ClickError> {
    lower_composite_resource_facts_with_bindings(
        definition,
        predicate_environment,
        click_function_environment,
        &[],
        &BTreeMap::new(),
        struct_layouts,
    )
}

pub(in crate::surface) fn lower_composite_resource_facts_with_bindings(
    definition: &ResourceDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    bindings: &[(String, ClickType)],
    integer_binding_variables: &BTreeMap<String, crate::kernel::Variable>,
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
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
        parameter_pointer_element_widths: click_parameter_pointer_element_widths_with_layouts(
            definition.parameters(),
            struct_layouts,
        ),
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
    let mut environment = SpecElaborationContext::default();
    for (name, variable) in integer_binding_variables {
        environment.integer_values.insert(
            name.clone(),
            crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(*variable)),
        );
    }
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
                    .click_proposition_to_spec_proposition(fact, &environment)
                    .map_err(ClickError::new)?,
            );
        }
        facts.push(
            lowerer
                .click_proposition_to_spec_proposition(&unfolded, &environment)
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
    annotated_function_with_assumptions(
        function_block,
        parsed_function,
        entry_state,
        arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
        None,
    )
}

/// What a re-annotation needs to re-establish a resource-derived loop frame.
///
/// The frame comes from the contract's one checked entry transition, so it
/// must be evaluated at the function's checked entry state and under its
/// entry facts. A proof that unfolds a consumed instance before it executes
/// leaves the frontier's own start state without that instance, and the
/// frontier is then not a legal place to re-evaluate the transition.
#[derive(Clone, Copy)]
pub(in crate::surface) struct ResourceFrameEntry<'a> {
    pub(in crate::surface) assumptions: &'a crate::kernel::PureFactContext,
    /// The checked function-entry state, when the proof recorded one. It is
    /// already argument-bound, so the annotation uses it as it stands.
    pub(in crate::surface) checked_entry_state: Option<&'a CState>,
}

pub(in crate::surface) fn annotated_function_with_assumptions(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    entry_state: &CState,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    frame_entry: Option<ResourceFrameEntry<'_>>,
) -> Result<CFunction, ClickError> {
    let (resource_requires, resource_ensures) =
        function_resource_summary(function_block, parsed_function, resource_environment)?;
    let resource_constructors = function_resource_constructors(function_block)?;
    let (
        contract_requires,
        contract_requirement_sources,
        contract_ensures,
        contract_mutable,
        resource_derived_mutable,
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
    let resource_derived_mutable_frame = function_block
        .requires()
        .iter()
        .any(|requirement| matches!(requirement.inner(), Requirement::Resource(_)));
    // `consumes` grants the callee a write-capable owned range. Carry that
    // frame into loop summaries so checked proof artifacts retain the same
    // memory-footprint evidence as independent contract certification. A
    // derived function inherits only its separately tracked resource frame.
    let implicit_contract_mutable_segments = if resource_derived_mutable_frame {
        resource_derived_mutable.as_slice()
    } else {
        contract_mutable.as_slice()
    };
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
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
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
        )
        .with_contract_requirement_sources(contract_requirement_sources);
    let function = function.with_resource_derived_mutable_segments(resource_derived_mutable);
    let function = if resource_derived_mutable_frame {
        let function = function.with_resource_derived_mutable_frame();
        if !function_block.is_external()
            && let Some(frame_entry) = frame_entry
        {
            let checked_entry = match frame_entry.checked_entry_state {
                Some(state) => state.clone(),
                None => crate::kernel::c_function_entry_state(entry_state, &function, arguments)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "could not construct the resource-derived loop entry for `{}`",
                            parsed_function.name()
                        ))
                    })?,
            };
            let mut budget = crate::kernel::ExecutionBudget::default();
            match crate::kernel::establish_resource_derived_loop_frames(
                function,
                &checked_entry,
                frame_entry.assumptions,
                &mut budget,
            ) {
                Ok(Ok(function)) => function,
                Ok(Err(message)) => {
                    return Err(ClickError::new(format!(
                        "could not establish resource-derived loop frames for `{}`: {message}",
                        parsed_function.name()
                    )));
                }
                Err(limit) => {
                    return Err(ClickError::new(format!(
                        "resource-derived loop-frame establishment for `{}` exceeded its execution budget: {limit:?}",
                        parsed_function.name()
                    )));
                }
            }
        } else {
            function
        }
    } else {
        function
    };
    if let Some(parameter) =
        crate::kernel::modified_by_value_aggregate_parameter_with_current_ensure_in_source(
            &function,
        )
    {
        return Err(ClickError::new(format!(
            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
        )));
    }
    Ok(function)
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
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
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
    parameter_pointer_element_widths: BTreeMap<String, u32>,
) -> (AnnotationLowerer<'a>, SpecElaborationContext) {
    let lowerer = AnnotationLowerer {
        structural_clauses: &[],
        predicate_environment,
        click_function_environment,
        entry_state,
        result_type: result.map(CValue::c_type).unwrap_or(CType::Int32),
        entry_values,
        parameter_array_element_types: array_element_types,
        parameter_pointer_element_widths,
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
    pointer_element_widths: BTreeMap<String, u32>,
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
        pointer_element_widths,
    );
    let mut context = context;
    context.algebraic_values = algebraic_values.into_iter().collect();
    context.integer_values = integer_values.clone();
    // Reserve only captured Integer values referenced by this proposition.
    // This one source walk keeps nested binders from rescanning the context.
    let mut referenced = BTreeSet::new();
    collect_click_proposition_referenced_names(proposition, &mut referenced);
    for name in referenced {
        if let Some(crate::kernel::SpecIntegerExpression::Term(term)) = integer_values.get(&name)
            && let Some(variable) = term.max_variable()
        {
            lowerer.next_quantifier_variable = lowerer.next_quantifier_variable.max(
                variable
                    .0
                    .checked_add(1)
                    .ok_or("quantifier variable identity exhausted")?,
            );
        }
    }
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
    pointer_element_widths: BTreeMap<String, u32>,
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
        pointer_element_widths,
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
    elaborate_fixed_state_integer_expression_with_integer_values(
        expression,
        array_element_types,
        entry_state,
        entry_values,
        current_values,
        &crate::persistent::PersistentMap::default(),
        result,
        snapshots,
        assumptions,
        predicate_environment,
        click_function_environment,
        opaque_click_functions,
        BTreeMap::new(),
    )
}

/// Elaborates a fixed-state Integer expression with already captured
/// mathematical bindings in scope.  The ordinary helper above is used for
/// expressions whose Integer names are all introduced by the expression
/// itself; theorem application also needs to preserve caller Integer
/// parameters and checked-proof locals while capturing a fold argument.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_integer_expression_with_integer_values(
    expression: &ContractExpression,
    array_element_types: BTreeMap<String, CType>,
    entry_state: &CState,
    entry_values: BTreeMap<String, CValue>,
    current_values: BTreeMap<String, CValue>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    result: Option<&CValue>,
    snapshots: &RecordedSnapshots,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
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
        pointer_element_widths,
    );
    let mut context = context;
    let referenced_names =
        crate::surface::lowering::contract_expression_referenced_names(expression);
    let mut referenced_integer_values = crate::persistent::PersistentMap::default();
    for name in referenced_names {
        if let Some(value) = integer_values.get(&name) {
            referenced_integer_values =
                referenced_integer_values.with_inserted(name, value.clone());
        }
    }
    context.integer_values = referenced_integer_values.clone();

    // Fold binders allocate from the fixed-state elaborator's local range.
    // Reserve identities already present in captured Integer arguments so a
    // fold's accumulator or item cannot capture a caller value.
    for (_, value) in referenced_integer_values.iter() {
        if let Some(variable) = max_spec_integer_expression_variable(value) {
            lowerer.next_quantifier_variable = lowerer.next_quantifier_variable.max(
                variable
                    .0
                    .checked_add(1)
                    .ok_or("quantifier variable identity exhausted")?,
            );
        }
    }
    lowerer.lower_contract_integer_to_spec(expression, &context)
}

/// Finds the largest variable identity nested in a captured Integer binding.
/// The kernel visitor includes free identities, quantifier identities, fold
/// binders, and identities nested in machine/C payloads. Keeping this query
/// here makes the lowering path independent of the visitor's representation.
fn max_spec_integer_expression_variable(
    expression: &crate::kernel::SpecIntegerExpression,
) -> Option<crate::kernel::Variable> {
    let mut variables = BTreeSet::new();
    crate::kernel::collect_spec_integer_bound_variables(expression, &mut variables);
    variables.into_iter().next_back()
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
    pointer_element_widths: BTreeMap<String, u32>,
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
        pointer_element_widths,
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
        parameter_pointer_element_widths: parameter_pointer_element_widths(parameters),
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
    _resource_environment: &ResourceEnvironment,
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
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
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
    let mut contract_requirement_sources = Vec::new();
    for proposition in requirement_definedness_surfaces(function_block.requires()) {
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => {
                requires.push(proposition);
                contract_requirement_sources.push(None);
            }
            Err(_) => opaque_contract_supported = false,
        }
    }
    for (source_index, requirement) in function_block.requires().iter().enumerate() {
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
                requires.push(proposition);
                contract_requirement_sources.push(Some(source_index));
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
    let mut resource_derived_mutable = Vec::new();
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
        // Keep the lowered owned segments separate from startup/explicit
        // metadata. The kernel's modular-call projection derives authority
        // from checked resource facts; these segments are only for body and
        // loop proof framing after their equivalence is checked.
        for requirement in function_block.requires() {
            if let Requirement::Resource(resource) = requirement.inner() {
                collect_owned_resource_memory_segments(
                    resource,
                    _resource_environment,
                    parsed_function.parameters(),
                    &mut lowerer,
                    &mut resource_derived_mutable,
                )?;
            }
        }
        mutable.extend(resource_derived_mutable.iter().cloned());
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
        contract_requirement_sources,
        ensures,
        mutable,
        resource_derived_mutable,
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
            let resource = &loop_resource_with_field_schema(resource, resource_environment)?;
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

/// A loop binder's checked field schema, taken from the resource definition
/// it names.
///
/// Contract binders are given their schema when the file is checked, because
/// a contract clause is reached from the function block. A loop binder lives
/// inside a proof script and is reached only here, at the one place its
/// declaration is lowered.
fn loop_resource_with_field_schema(
    resource: &ResourceClause,
    resource_environment: &ResourceEnvironment,
) -> Result<ResourceClause, ClickError> {
    let ResourceClause::Named { binding, resource } = resource else {
        return Ok(resource.clone());
    };
    if binding.schema.is_some() {
        return Ok(ResourceClause::Named {
            binding: binding.clone(),
            resource: resource.clone(),
        });
    }
    let ResourceClause::Declared { name, .. } = resource.as_ref() else {
        return Err(ClickError::new(
            "named ownership requires a declared resource",
        ));
    };
    let schema = resource_environment
        .get(name)
        .and_then(ResourceDefinition::field_schema)
        .ok_or_else(|| {
            ClickError::new(format!(
                "loop binder `{}` names resource `{name}`, which has no checked fields",
                binding.name
            ))
        })?;
    Ok(ResourceClause::Named {
        binding: ResourceInstanceBinding {
            schema: Some(schema.clone()),
            ..binding.clone()
        },
        resource: resource.clone(),
    })
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
    /// Source-side pointee widths which are not representable in the kernel's
    /// nominal `CType` (notably pointers to structs, which use the compatible
    /// `int32*` carrier).  Pointer arithmetic must retain this physical width.
    parameter_pointer_element_widths: BTreeMap<String, u32>,
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

pub(in crate::surface) fn parameter_pointer_element_widths(
    parameters: &[syntax::C0Parameter],
) -> BTreeMap<String, u32> {
    parameters
        .iter()
        .filter_map(|parameter| {
            parameter
                .array_element_width()
                .or_else(|| {
                    parameter
                        .pointee_struct_layout()
                        .map(|layout| layout.size_bytes())
                })
                .or_else(|| parameter.struct_layout().map(|layout| layout.size_bytes()))
                .map(|width| (parameter.name().to_string(), width))
        })
        .collect()
}

/// Widths which remain knowable for Click-defined resource parameters. Such
/// parameters retain array element types, while a struct-pointer parameter's
/// layout is unavailable outside the C translation unit.
pub(in crate::surface) fn click_parameter_pointer_element_widths_with_layouts(
    parameters: &[FunctionParameter],
    struct_layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> BTreeMap<String, u32> {
    parameters
        .iter()
        .filter_map(|parameter| {
            parameter
                .struct_name()
                .and_then(|name| struct_layouts.get(name))
                .map(|layout| (parameter.name().to_string(), layout.size_bytes()))
                .or_else(|| {
                    parameter
                        .click_type()
                        .c_type()
                        .and_then(click_array_element_type)
                        .map(|element| (parameter.name().to_string(), element.byte_width()))
                })
        })
        .collect()
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
                let (ranking_measures, structural_measure) =
                    self.loop_measure_clauses(loop_index)?;
                if matches!(statement, syntax::C0Statement::DoWhile { .. }) {
                    c_do_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_loop_resource_specs(resource_specs)
                    .with_loop_ranking_measures(ranking_measures)
                    .with_loop_structural_measure(structural_measure)
                } else {
                    c_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_loop_resource_specs(resource_specs)
                    .with_loop_ranking_measures(ranking_measures)
                    .with_loop_structural_measure(structural_measure)
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
                let (ranking_measures, structural_measure) =
                    self.loop_measure_clauses(loop_index)?;
                c_seq(
                    lowered_initializer,
                    c_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        crate::kernel::c_for_body_with_step(lowered_body, lowered_step),
                    )
                    .with_loop_resource_specs(resource_specs)
                    .with_loop_ranking_measures(ranking_measures)
                    .with_loop_structural_measure(structural_measure),
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

    /// The loop's declared `decreases` components, in source order.
    ///
    /// The measure travels on the loop head so the back-edge invariant
    /// bundle, the verified loop rule, and the whole-function termination
    /// pass all read the one declared clause rather than agreeing by
    /// coincidence.
    fn loop_ranking_measures(
        &self,
        loop_index: usize,
    ) -> Result<Option<crate::kernel::CLoopTerminationMeasure>, ClickError> {
        let mut measures: Option<crate::kernel::CLoopTerminationMeasure> = None;
        for clause in self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
        {
            let Some(expressions) = crate::surface::verification::loop_termination_measure(
                clause,
                &format!("loop {loop_index} `decreases`"),
            )?
            else {
                continue;
            };
            match &measures {
                Some(existing) if existing != &expressions => {
                    return Err(ClickError::new(format!(
                        "loop {loop_index} has conflicting `decreases` measures"
                    )));
                }
                _ => measures = Some(expressions),
            }
        }
        Ok(measures)
    }

    /// The loop head's declared measure, split into the two clauses the
    /// kernel loop statement carries.
    fn loop_measure_clauses(
        &self,
        loop_index: usize,
    ) -> Result<(Vec<CExpression>, Option<String>), ClickError> {
        Ok(match self.loop_ranking_measures(loop_index)? {
            Some(crate::kernel::CLoopTerminationMeasure::Ranking(components)) => (components, None),
            Some(crate::kernel::CLoopTerminationMeasure::Structural(binder)) => {
                (Vec::new(), Some(binder))
            }
            None => (Vec::new(), None),
        })
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
                written_name,
                body,
            } => {
                let display_name = written_name.as_ref().unwrap_or(name);
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable = self
                    .next_quantifier_variable
                    .checked_add(1)
                    .ok_or("quantifier variable identity exhausted")?;
                let mut body_environment = environment.clone();
                body_environment.integer_values.remove(name);
                body_environment.values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                if *c_type == ClickType::Integer {
                    body_environment.integer_values.insert(
                        name.clone(),
                        crate::kernel::SpecIntegerExpression::Term(
                            crate::kernel::IntegerTerm::var(variable),
                        ),
                    );
                    let body =
                        self.click_proposition_to_spec_proposition(body, &body_environment)?;
                    return Ok(SpecProposition::ForAllInteger {
                        name: display_name.clone(),
                        variable,
                        body: Box::new(body),
                    });
                }
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
                        name: display_name.clone(),
                        variable,
                        body: Box::new(body),
                    })
                } else {
                    Ok(SpecProposition::ForAllPointer {
                        name: display_name.clone(),
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
                written_name,
                body,
            } => {
                let display_name = written_name.as_ref().unwrap_or(name);
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable = self
                    .next_quantifier_variable
                    .checked_add(1)
                    .ok_or("quantifier variable identity exhausted")?;
                let mut body_environment = environment.clone();
                body_environment.integer_values.remove(name);
                body_environment.values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                if *c_type == ClickType::Integer {
                    body_environment.integer_values.insert(
                        name.clone(),
                        crate::kernel::SpecIntegerExpression::Term(
                            crate::kernel::IntegerTerm::var(variable),
                        ),
                    );
                    let body =
                        self.click_proposition_to_spec_proposition(body, &body_environment)?;
                    return Ok(SpecProposition::ExistsInteger {
                        name: display_name.clone(),
                        variable,
                        body: Box::new(body),
                    });
                }
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
                        name: display_name.clone(),
                        variable,
                        body: Box::new(body),
                    })
                } else {
                    Ok(SpecProposition::ExistsPointer {
                        name: display_name.clone(),
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
                written_item,
                body,
            } => {
                let display_item = written_item.as_ref().unwrap_or(item);
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
                    name: display_item.clone(),
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
                written_item,
                body,
            } => {
                let display_item = written_item.as_ref().unwrap_or(item);
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
                    name: display_item.clone(),
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

    /// The value a fixed snapshot gives one resource field.
    ///
    /// Only an explicit `at(...)` snapshot fixes one. That snapshot names a
    /// state, so a field the instance does not hold there is an error: no
    /// other reading exists.
    ///
    /// `old(...)` is not a named state but the function entry, and a binder's
    /// entry field always has a symbolic reading of its own -- the kernel's
    /// entry projection, which the caller emits when this answers `None`.
    /// Reading it out of whatever state this lowering was handed instead made
    /// `old(name.field)` in a loop invariant mean the generation that state
    /// held, so a proof that unfolded and refolded the binder before the loop
    /// changed what `old(...)` meant, and the frontier and contract
    /// certification lowered the same invariant two ways.
    fn fixed_resource_field(
        &self,
        access: &ResourceFieldAccess,
        environment: &SpecElaborationContext,
    ) -> Result<Option<AlgebraicValue>, String> {
        if let Some(state) = environment.snapshot_state.as_ref() {
            return state
                .resource_instance_at_path(access.identity, &access.children)
                .and_then(|instance| instance.fields().get(access.field_index))
                .cloned()
                .map(Some)
                .ok_or_else(|| {
                    format!(
                        "resource instance `{}` is not owned at this snapshot",
                        access.owner
                    )
                });
        }
        Ok(None)
    }

    fn contract_expression_is_integer(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> bool {
        self.contract_expression_click_type(expression, environment)
            .is_some_and(|click_type| click_type == ClickType::Integer)
    }

    /// Infer the result kind needed when choosing between the C and Integer
    /// lowering paths.  Surface validation already checks algebraic match
    /// arms against their datatype schema, but the fixed-state lowerer does
    /// not retain that result type in the syntax tree.  Recover it here so a
    /// match whose arms return an Integer binding is still recognized when
    /// the other comparison operand is an untyped numeral.
    fn contract_expression_click_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Option<ClickType> {
        self.contract_expression_click_type_in_scope(expression, environment, &mut Vec::new())
    }

    fn contract_expression_click_type_in_scope(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
        lexical_bindings: &mut Vec<(String, Option<ClickType>)>,
    ) -> Option<ClickType> {
        match expression {
            ContractExpression::ResourceField(access) => access.click_type.clone(),
            ContractExpression::IntegerLiteral(_) => None,
            ContractExpression::Binding(name) => {
                if let Some((_, click_type)) = lexical_bindings
                    .iter()
                    .rev()
                    .find(|(binding, _)| binding == name)
                {
                    click_type.clone()
                } else if environment.integer_values.contains_key(name) {
                    Some(ClickType::Integer)
                } else if let Some(value) = environment.algebraic_values.get(name) {
                    Some(generics::click_type_from_algebraic_value_type(
                        &value.algebraic_type.value_type(),
                    ))
                } else {
                    environment
                        .values
                        .get(name)
                        .and_then(spec_expression_click_type)
                }
            }
            ContractExpression::AlgebraicVariable { algebraic_type, .. }
            | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
                Some(ClickType::Algebraic(algebraic_type.clone()))
            }
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => self.contract_expression_click_type_in_scope(inner, environment, lexical_bindings),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => {
                let left = self.contract_expression_click_type_in_scope(
                    left,
                    environment,
                    lexical_bindings,
                );
                let right = self.contract_expression_click_type_in_scope(
                    right,
                    environment,
                    lexical_bindings,
                );
                if left == Some(ClickType::Integer) || right == Some(ClickType::Integer) {
                    Some(ClickType::Integer)
                } else {
                    left.or(right)
                }
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
                ..
            } => {
                // The index carrier and accumulator carrier are independent.
                // In particular, an Int32 index can feed a C array load while
                // `to_integer(...)` makes the accumulator mathematical.  A
                // fold's result follows the accumulator/body type; the
                // endpoint type only selects the item carrier in the body.
                let start_type = self.contract_expression_click_type_in_scope(
                    start,
                    environment,
                    lexical_bindings,
                );
                let end_type = self.contract_expression_click_type_in_scope(
                    end,
                    environment,
                    lexical_bindings,
                );
                let integer_index =
                    start_type == Some(ClickType::Integer) || end_type == Some(ClickType::Integer);
                let initial_type = self.contract_expression_click_type_in_scope(
                    initial,
                    environment,
                    lexical_bindings,
                );
                let lexical_len = lexical_bindings.len();
                let accumulator_type = initial_type.clone();
                lexical_bindings.push((accumulator.clone(), accumulator_type));
                lexical_bindings.push((
                    item.clone(),
                    if integer_index {
                        Some(ClickType::Integer)
                    } else {
                        Some(ClickType::C(C0Type::Int32))
                    },
                ));
                let body_type = self.contract_expression_click_type_in_scope(
                    body,
                    environment,
                    lexical_bindings,
                );
                lexical_bindings.truncate(lexical_len);
                if initial_type == Some(ClickType::Integer) || body_type == Some(ClickType::Integer)
                {
                    Some(ClickType::Integer)
                } else {
                    initial_type.or(body_type)
                }
            }
            ContractExpression::CFragment(CExpression::Variable(name))
            | ContractExpression::CBinding(name) => {
                if let Some((_, click_type)) = lexical_bindings
                    .iter()
                    .rev()
                    .find(|(binding, _)| binding == name)
                {
                    click_type.clone()
                } else if environment.integer_values.contains_key(name) {
                    Some(ClickType::Integer)
                } else {
                    environment
                        .values
                        .get(name)
                        .and_then(spec_expression_click_type)
                }
            }
            ContractExpression::Let {
                name,
                click_type: Some(ClickType::Integer),
                value: _,
                body,
            } => {
                lexical_bindings.push((name.clone(), Some(ClickType::Integer)));
                let body_type = self.contract_expression_click_type_in_scope(
                    body,
                    environment,
                    lexical_bindings,
                );
                lexical_bindings.pop();
                body_type
            }
            ContractExpression::Let {
                name,
                click_type: _,
                value,
                body,
            } => {
                let value_type = self.contract_expression_click_type_in_scope(
                    value,
                    environment,
                    lexical_bindings,
                );
                lexical_bindings.push((name.clone(), value_type));
                let body_type = self.contract_expression_click_type_in_scope(
                    body,
                    environment,
                    lexical_bindings,
                );
                lexical_bindings.pop();
                body_type
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                let Some(ClickType::Algebraic(application)) = self
                    .contract_expression_click_type_in_scope(
                        scrutinee,
                        environment,
                        lexical_bindings,
                    )
                else {
                    return None;
                };
                let Ok(algebraic_type) =
                    algebraic_kernel_type(self.click_function_environment, &application)
                else {
                    return None;
                };
                let variants = algebraic_type
                    .variants
                    .iter()
                    .map(|variant| (variant.name.as_str(), variant))
                    .collect::<BTreeMap<_, _>>();
                crate::instrumentation::record_deterministic_work(algebraic_type.variants.len());
                let mut result_type = None;
                let mut has_contextual_literal = false;
                for arm in arms {
                    crate::instrumentation::record_deterministic_work(1);
                    let variant = variants.get(arm.variant.as_str())?;
                    if arm.bindings.len() != variant.fields.len() {
                        return None;
                    }
                    let lexical_len = lexical_bindings.len();
                    for (binding, field) in arm.bindings.iter().zip(&variant.fields) {
                        lexical_bindings.push((
                            binding.clone(),
                            Some(generics::click_type_from_algebraic_value_type(field)),
                        ));
                    }
                    let arm_type = self.contract_expression_click_type_in_scope(
                        &arm.body,
                        environment,
                        lexical_bindings,
                    );
                    lexical_bindings.truncate(lexical_len);
                    let Some(arm_type) = arm_type else {
                        if is_unsuffixed_integer_literal_expression(&arm.body) {
                            // A numeral arm stays untyped until another arm
                            // supplies the match result carrier.  In
                            // particular, do not make an all-literal match
                            // mathematical Integer by default.
                            has_contextual_literal = true;
                            continue;
                        }
                        return None;
                    };
                    if let Some(previous) = &result_type
                        && previous != &arm_type
                    {
                        return None;
                    }
                    result_type = Some(arm_type);
                }
                if has_contextual_literal
                    && !matches!(
                        result_type.as_ref(),
                        Some(ClickType::Integer) | Some(ClickType::C(_))
                    )
                {
                    return None;
                }
                result_type
            }
            ContractExpression::Call { name, .. } if name == "to_integer" => {
                Some(ClickType::Integer)
            }
            ContractExpression::Call { name, .. } => self
                .click_function_environment
                .get(name)
                .map(|function| function.return_type().clone()),
            _ => None,
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
            let mut lowered_arms = Vec::new();
            let mut seen = std::collections::BTreeSet::new();
            for arm in arms {
                if !seen.insert(arm.variant.clone()) {
                    return Err(format!("duplicate match arm `{}`", arm.variant));
                }
                let variant = scrutinee
                    .algebraic_type
                    .variants
                    .iter()
                    .find(|variant| variant.name == arm.variant)
                    .ok_or_else(|| format!("unknown match variant `{}`", arm.variant))?;
                if arm.bindings.len() != variant.fields.len() {
                    return Err(format!(
                        "match arm `{}` has the wrong number of bindings",
                        arm.variant
                    ));
                }
                let mut body_environment = environment.clone();
                for (binding, binding_type) in arm.bindings.iter().zip(&variant.fields) {
                    match binding_type {
                        AlgebraicValueType::C(_) => {
                            body_environment.integer_values.remove(binding);
                            body_environment.algebraic_values.remove(binding);
                            body_environment.values.insert(
                                binding.clone(),
                                crate::kernel::SpecExpression::CExpression(
                                    crate::kernel::CExpression::Variable(binding.clone()),
                                ),
                            );
                        }
                        AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_) => {
                            body_environment.values.remove(binding);
                            body_environment.integer_values.remove(binding);
                            body_environment.algebraic_values.insert(
                                binding.clone(),
                                crate::kernel::SpecAlgebraicExpression {
                                    algebraic_type: self
                                        .cached_algebraic_kernel_type_from_value_type(
                                            binding_type,
                                        )?,
                                    node: crate::kernel::SpecAlgebraicExpressionNode::Binding(
                                        binding.clone(),
                                    ),
                                },
                            );
                        }
                        AlgebraicValueType::Integer => {
                            body_environment.values.remove(binding);
                            body_environment.algebraic_values.remove(binding);
                            let variable = crate::kernel::Variable(self.next_quantifier_variable);
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
                let body = self.lower_contract_integer_to_spec(&arm.body, &body_environment)?;
                lowered_arms.push(crate::kernel::SpecIntegerMatchArm {
                    variant: arm.variant.clone(),
                    bindings: arm.bindings.clone(),
                    binding_types: variant.fields.clone(),
                    binding_variables: arm
                        .bindings
                        .iter()
                        .zip(&variant.fields)
                        .map(|(binding, binding_type)| {
                            if binding_type == &AlgebraicValueType::Integer {
                                match body_environment.integer_values.get(binding) {
                                    Some(crate::kernel::SpecIntegerExpression::Term(
                                        crate::kernel::IntegerTerm::Variable(variable),
                                    )) => Some(*variable),
                                    _ => None,
                                }
                            } else {
                                None
                            }
                        })
                        .collect(),
                    body: Box::new(body),
                });
            }
            if seen.len() != scrutinee.algebraic_type.variants.len() {
                return Err("symbolic Integer-valued datatype matches must be exhaustive".into());
            }
            return Ok(SpecIntegerExpression::AlgebraicMatch {
                scrutinee: Box::new(scrutinee),
                arms: lowered_arms,
            });
        }
        // The proof parser preserves a variable reference as a C fragment
        // until contextual typing identifies it as an Integer.  Resolve it
        // through the active scoped environment so fold accumulator and
        // captured Integer references retain their preallocated kernel terms.
        if let ContractExpression::CFragment(CExpression::Variable(name)) = expression
            && let Some(value) = environment.integer_values.get(name)
        {
            return Ok(value.clone());
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
                if self.contract_expression_is_integer(argument, environment) {
                    return Err("to_integer expects a machine integer or Nat".to_string());
                }
                if let Ok(nat) = self.lower_contract_algebraic_to_spec(argument, environment)
                    && crate::kernel::is_conversion_nat_type(&nat.algebraic_type)
                {
                    return Ok(SpecIntegerExpression::PureFunctionApplication {
                        name: "to_integer".to_string(),
                        arguments: vec![crate::kernel::SpecPureFunctionArgument::Algebraic(nat)],
                    });
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
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let initial = self.lower_contract_integer_to_spec(initial, environment)?;
                let accumulator_variable = crate::kernel::Variable(self.next_quantifier_variable);
                self.next_quantifier_variable = self.next_quantifier_variable.saturating_add(1);
                let item_variable = crate::kernel::Variable(self.next_quantifier_variable);
                self.next_quantifier_variable = self.next_quantifier_variable.saturating_add(1);
                let integer_expression = |expression: &ContractExpression| {
                    fn is_integer(
                        expression: &ContractExpression,
                        environment: &SpecElaborationContext,
                        functions: &ClickFunctionEnvironment,
                    ) -> bool {
                        match expression {
                            ContractExpression::Binding(name)
                            | ContractExpression::CFragment(CExpression::Variable(name))
                            | ContractExpression::CBinding(name) => {
                                environment.integer_values.contains_key(name)
                            }
                            ContractExpression::ResourceField(access) => {
                                access.click_type == Some(ClickType::Integer)
                            }
                            ContractExpression::Call { name, .. } => {
                                functions.get(name).is_some_and(|function| {
                                    function.return_type() == &ClickType::Integer
                                })
                            }
                            ContractExpression::Add(left, right)
                            | ContractExpression::Subtract(left, right)
                            | ContractExpression::Multiply(left, right) => {
                                is_integer(left, environment, functions)
                                    || is_integer(right, environment, functions)
                            }
                            _ => false,
                        }
                    }
                    is_integer(expression, environment, self.click_function_environment)
                };
                let integer_index = integer_expression(start) || integer_expression(end);
                let mut body_environment = environment.clone();
                body_environment.integer_values.insert(
                    accumulator.clone(),
                    SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(
                        accumulator_variable,
                    )),
                );
                body_environment.integer_values.insert(
                    item.clone(),
                    SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(item_variable)),
                );
                if integer_index {
                    let start = self.lower_contract_integer_to_spec(start, environment)?;
                    let end = self.lower_contract_integer_to_spec(end, environment)?;
                    let body = self.lower_contract_integer_to_spec(body, &body_environment)?;
                    return Ok(SpecIntegerExpression::RangeFold {
                        index: crate::kernel::SpecIntegerRangeFoldIndex::Integer {
                            start: Box::new(start),
                            end: Box::new(end),
                        },
                        initial: Box::new(initial),
                        accumulator: accumulator_variable,
                        item: item_variable,
                        body: Box::new(body),
                    });
                }
                body_environment.integer_values.remove(item);
                body_environment.values.insert(
                    item.clone(),
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(item_variable))),
                );
                let body = self.lower_contract_integer_to_spec(body, &body_environment)?;
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                Ok(SpecIntegerExpression::RangeFold {
                    index: crate::kernel::SpecIntegerRangeFoldIndex::Int32 {
                        start: Box::new(start),
                        end: Box::new(end),
                    },
                    initial: Box::new(initial),
                    accumulator: accumulator_variable,
                    item: item_variable,
                    body: Box::new(body),
                })
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
            }
            | ContractExpression::ArrayIndex {
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
                let fixed = match self.fixed_resource_field(access, environment)? {
                    Some(AlgebraicValue::Algebraic(AlgebraicTerm {
                        node: AlgebraicTermNode::Variable(variable),
                        ..
                    })) => Some(variable),
                    // A named snapshot has only the value it holds; the
                    // function entry also has its symbolic projection.
                    Some(_) if environment.snapshot_state.is_some() => {
                        return Err("only entry-bound symbolic resource fields support fixed snapshots in this slice".into());
                    }
                    Some(_) | None => None,
                };
                let node = if let Some(variable) = fixed {
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
        let memory_independent = self
            .click_function_environment
            .is_memory_independent(definition.name());
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
                // The C null pointer constant stands at a pointer-typed pure
                // parameter and lowers to that pointer type's null value, not
                // to an `int32` zero, so `rb_parent_is(sub, 0)` compares the
                // model's parent payload with a pointer.
                ClickType::C(c_type)
                    if crate::surface::lowering::argument_is_null_pointer_constant(
                        argument, *c_type,
                    ) =>
                {
                    let pointer = SpecExpression::Value(CValue::typed_pointer(
                        crate::kernel::Pointer::null(),
                        c_type.to_kernel_type(),
                    ));
                    Ok(match click_array_element_type(*c_type) {
                        Some(element_type) => crate::kernel::SpecPureFunctionArgument::ArrayRef {
                            memory: if memory_independent {
                                crate::kernel::SpecMemory::Fixed(
                                    crate::kernel::value_independent_click_memory(),
                                )
                            } else {
                                environment.current_memory.clone()
                            },
                            pointer,
                            element_type,
                        },
                        None => crate::kernel::SpecPureFunctionArgument::Value(pointer),
                    })
                }
                ClickType::C(_) if parameter_is_click_array_ref(parameter) => {
                    let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                    Ok(crate::kernel::SpecPureFunctionArgument::ArrayRef {
                        // A function that reads no memory is a function of
                        // its argument values, so its pointer arguments are
                        // anchored to one canonical snapshot instead of the
                        // ambient one. Without this the same proposition is a
                        // different term on either side of a C write, and a
                        // `fold` cannot discharge a body fact that applies a
                        // pure predicate to a pointer (gap 42).
                        memory: if memory_independent {
                            crate::kernel::SpecMemory::Fixed(
                                crate::kernel::value_independent_click_memory(),
                            )
                        } else {
                            array_ref.memory
                        },
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
                if let Some(element_width) =
                    self.c_expression_array_element_width(left, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                        elements: Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                        byte_width: element_width,
                    });
                }
                if let Some(element_width) =
                    self.c_expression_array_element_width(right, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                        elements: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                        byte_width: element_width,
                    });
                }
                Ok(SpecExpression::Add(
                    Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                    Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                ))
            }
            CExpression::Subtract(left, right) => {
                if let Some(element_width) =
                    self.c_expression_array_element_width(left, environment)
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
                        byte_width: element_width,
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
            // A pointer-to-integer cast still has to lower pointer arithmetic
            // in its operand.  Keeping the whole cast as a raw C expression
            // would make the kernel infer the nominal carrier width for a
            // struct pointer (four bytes), losing the source layout width.
            CExpression::Cast {
                expression,
                target_type,
                ..
            } if *target_type == CType::UInt64
                && self
                    .c_expression_array_element_width(expression, environment)
                    .is_some() =>
            {
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

    /// The physical width used by C pointer arithmetic.  A pointer to a
    /// struct has the nominal compatible `int32*` kernel carrier, so its
    /// pointee layout must be consulted before falling back to `CType`.
    fn c_expression_array_element_width(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Option<u32> {
        match expression {
            CExpression::Value(CValue::Pointer(pointer)) => {
                pointer.c_type().pointee_type().map(CType::byte_width)
            }
            CExpression::Cast { target_type, .. } => {
                target_type.pointee_type().map(CType::byte_width)
            }
            CExpression::Variable(name) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type.byte_width())
                .or_else(|| self.parameter_pointer_element_widths.get(name).copied())
                .or_else(|| {
                    self.parameter_array_element_types
                        .get(name)
                        .map(|ty| ty.byte_width())
                })
                .or_else(|| {
                    (name == "result")
                        .then(|| self.result_type.pointee_type())
                        .flatten()
                        .map(CType::byte_width)
                })
                .or_else(|| {
                    self.entry_state
                        .global_array_element_type(name)
                        .map(CType::byte_width)
                })
                .or_else(|| {
                    environment.values.get(name).and_then(|value| match value {
                        SpecExpression::Value(CValue::Pointer(pointer)) => {
                            pointer.c_type().pointee_type().map(CType::byte_width)
                        }
                        _ => None,
                    })
                }),
            CExpression::TypedLoad { value_type, .. } => match value_type {
                CType::Int32Array(_) => Some(4),
                CType::UInt8Array(_) => Some(1),
                value_type => value_type.pointee_type().map(CType::byte_width),
            },
            CExpression::PointerOffsetBytes { pointer, .. } => {
                self.c_expression_array_element_width(pointer, environment)
            }
            CExpression::Add(left, right) => self
                .c_expression_array_element_width(left, environment)
                .or_else(|| self.c_expression_array_element_width(right, environment)),
            CExpression::Subtract(left, _) => {
                self.c_expression_array_element_width(left, environment)
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
            checks.push(CLoopEffectCheck::new_with_origin(
                CLoopEffect::Mutable(declaration.owned_segments.clone()),
                CLoopEffectSpan::Whole,
                CLoopEffectOrigin::DeclaredResource,
                Some(format!("loop {loop_index} declared owned resource frame")),
            ));
        } else if self.inherits_resource_derived_frame
            || !self.implicit_contract_mutable_segments.is_empty()
        {
            checks.push(CLoopEffectCheck::new_with_origin(
                CLoopEffect::Mutable(self.implicit_contract_mutable_segments.to_vec()),
                CLoopEffectSpan::Whole,
                CLoopEffectOrigin::InheritedResourceDerived,
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
        AlgebraicFieldType::C { c_type, .. } => Ok(AlgebraicValueType::C(c_type.to_kernel_type())),
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

#[cfg(test)]
mod integer_source_quantifier_tests {
    use super::*;
    use crate::kernel::{IntegerTerm, SpecIntegerExpression};

    #[test]
    fn captured_integer_freshness_ignores_unrelated_heap_snapshot() {
        use crate::kernel::{
            Bitvector32Term, CMemory, CType, CValue, Pointer, PointerBlock, PointerOffsetTerm,
            SpecExpression, SpecMemory, SpecPureFunctionArgument,
        };

        let explicit = Variable(2_001);
        let unrelated_heap_variable = Variable(9_000_001);
        let heap_pointer = Pointer {
            block: PointerBlock::Heap(77),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new()
            .with_block(heap_pointer.block.clone(), 4)
            .store(
                heap_pointer,
                CValue::Int32(Bitvector32Term::Variable(unrelated_heap_variable)),
            );
        let captured_array = SpecIntegerExpression::PureFunctionApplication {
            name: "captured_array_value".to_string(),
            arguments: vec![SpecPureFunctionArgument::ArrayRef {
                memory: SpecMemory::Fixed(memory.clone()),
                pointer: SpecExpression::Value(CValue::pointer(Pointer::null())),
                element_type: CType::Int32,
            }],
        };
        let captured_from_machine_load =
            SpecIntegerExpression::FromMachine(Box::new(SpecExpression::MemoryLoad {
                memory: SpecMemory::Fixed(memory),
                pointer: Box::new(SpecExpression::Value(CValue::pointer(Pointer::null()))),
                value_type: CType::Int32,
            }));
        let captured = SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::Term(IntegerTerm::var(explicit))),
            Box::new(SpecIntegerExpression::Add(
                Box::new(captured_array),
                Box::new(captured_from_machine_load),
            )),
        );

        assert_eq!(
            max_spec_integer_expression_variable(&captured),
            Some(explicit),
            "freshness must follow explicit expression identities, not cells in an unrelated snapshot"
        );
    }

    #[test]
    fn integer_quantifier_does_not_capture_a_caller_binding() {
        let file = crate::surface::parse(
            "theorem capture(x: Integer) { ensures forall (z: Integer) { x == z }; }",
        )
        .unwrap();
        let Ensure::Proposition(proposition) = file.theorem_definitions()[0].ensures()[0].ensure()
        else {
            panic!("expected proposition")
        };
        let integer_values = [(
            "x".to_string(),
            SpecIntegerExpression::Term(IntegerTerm::var(Variable(2_000_000))),
        )]
        .into_iter()
        .collect();
        let state = CState::new();
        let lowered = elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
            proposition,
            BTreeMap::new(),
            &state,
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeMap::new(),
            &integer_values,
            None,
            &RecordedSnapshots::new(),
            &PureFactContext::new(),
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
            BTreeSet::new(),
            BTreeMap::new(),
        )
        .unwrap();
        let SpecProposition::ForAllInteger { variable, body, .. } = lowered else {
            panic!("expected Integer forall")
        };
        assert_ne!(variable, Variable(2_000_000));
        let SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(left),
            right: SpecIntegerExpression::Term(right),
            ..
        } = *body
        else {
            panic!("expected Integer comparison")
        };
        assert_eq!(left, IntegerTerm::var(Variable(2_000_000)));
        assert_eq!(right, IntegerTerm::var(variable));
    }
}
