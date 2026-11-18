use super::*;
use crate::kernel::{AlgebraicTerm, AlgebraicTermNode, LoopEffectOrigin};
use crate::kernel::{bits32_constant, constant_u32};

// The lowerers share these two finite bands. Refusing at each ceiling keeps
// quantifiers, algebraic binders, pointer identities, and spec fold binders
// structurally separate even for unusually large source terms.
const SURFACE_QUANTIFIER_VARIABLE_CEILING: u64 = 4_000_000;
const ALGEBRAIC_VARIABLE_BASE: u64 = SURFACE_QUANTIFIER_VARIABLE_CEILING;
const ALGEBRAIC_VARIABLE_CEILING: u64 = 4_000_000_000;
const ALGEBRAIC_BINDER_STRIDE: u64 = 65_536;

fn allocate_quantifier_variable(next: &mut u64) -> Result<Variable, String> {
    if *next >= SURFACE_QUANTIFIER_VARIABLE_CEILING {
        return Err("quantifier variable identity exhausted".to_string());
    }
    let variable = Variable(*next);
    *next += 1;
    Ok(variable)
}

pub(in crate::surface) fn algebraic_binder_variable(
    binder_index: usize,
) -> Result<Variable, String> {
    let index = u64::try_from(binder_index).map_err(|_| "too many algebraic binders")?;
    let identity = index
        .checked_mul(ALGEBRAIC_BINDER_STRIDE)
        .and_then(|offset| ALGEBRAIC_VARIABLE_BASE.checked_add(offset))
        .filter(|identity| *identity < ALGEBRAIC_VARIABLE_CEILING)
        .ok_or("too many algebraic binders")?;
    Ok(Variable(identity))
}

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
        // A state of a literal is the literal.
        ContractExpression::Negate(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => is_unsuffixed_integer_literal_expression(inner),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            is_unsuffixed_integer_literal_expression(left)
                && is_unsuffixed_integer_literal_expression(right)
        }
        _ => false,
    }
}

/// One loop's declared measure as the loop head carries it: the lowered
/// ranking components, or the resource binder a structural measure names.
#[derive(Clone, Debug, Eq, PartialEq)]
enum LoopMeasureClauses {
    Ranking(Vec<crate::kernel::RankingComponent>),
    Structural(String),
}

/// The state a `decreases` component names, when it names one at all.
///
/// A measure is read at two states, so a component that fixes its own state
/// is not a measure. This says which form fixed it, so the refusal can name
/// the spelling the user wrote.
enum FixedMeasureState {
    /// `old(...)`: the function's entry state.
    Old,
    /// `at(<selector>, ...)`: a recorded state, including a loop's entry.
    At(ProgramPointSelector),
}

impl FixedMeasureState {
    fn spelling(&self) -> String {
        match self {
            Self::Old => "old(...)".to_string(),
            Self::At(selector) => format!(
                "at({}, ...)",
                crate::surface::diagnostics::describe_program_point_selector(selector)
            ),
        }
    }
}

/// The fixed state one declared `decreases` component names, if any.
///
/// Work is linear in the component, which is the declared expression; nothing
/// ambient is walked.
fn fixed_measure_state(expression: &ContractExpression) -> Option<FixedMeasureState> {
    let either = |left: &ContractExpression, right: &ContractExpression| {
        fixed_measure_state(left).or_else(|| fixed_measure_state(right))
    };
    match expression {
        ContractExpression::IntegerContext(value) => fixed_measure_state(value),

        ContractExpression::Proposition(_) => None,
        ContractExpression::Resource(_) => None,
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => None,
        ContractExpression::Lambda { body, .. } => fixed_measure_state(body),
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            fixed_measure_state(function).or_else(|| arguments.iter().find_map(fixed_measure_state))
        }

        ContractExpression::Old(_) => Some(FixedMeasureState::Old),
        ContractExpression::At { selector, .. } => Some(FixedMeasureState::At(selector.clone())),
        ContractExpression::IntegerLiteral(_)
        | ContractExpression::QualifiedC { .. }
        | ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::ProgramBinding(_)
        | ContractExpression::ProgramExpression(_)
        | ContractExpression::CUnary { .. }
        | ContractExpression::ResourceWildcard => None,
        ContractExpression::AlgebraicConstructor { arguments, .. }
        | ContractExpression::Call { arguments, .. } => {
            arguments.iter().find_map(fixed_measure_state)
        }
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            fixed_measure_state(receiver).or_else(|| arguments.iter().find_map(fixed_measure_state))
        }
        ContractExpression::SequenceLiteral(elements) => {
            elements.iter().find_map(fixed_measure_state)
        }
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                arguments.iter().find_map(fixed_measure_state)
            }
            _ => None,
        },
        ContractExpression::AlgebraicMatch { scrutinee, arms } => fixed_measure_state(scrutinee)
            .or_else(|| arms.iter().find_map(|arm| fixed_measure_state(&arm.body))),
        ContractExpression::Field { base, .. }
        | ContractExpression::Negate(base)
        | ContractExpression::BitwiseNot(base) => fixed_measure_state(base),
        ContractExpression::ArrayIndex { base, .. } => fixed_measure_state(base),
        ContractExpression::SequenceConcat(left, right)
        | ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::RustShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::RustShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => either(left, right),
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => either(then_branch, else_branch),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => fixed_measure_state(start)
            .or_else(|| fixed_measure_state(end))
            .or_else(|| fixed_measure_state(initial))
            .or_else(|| fixed_measure_state(body)),
        ContractExpression::Let { value, body, .. } => either(value, body),
    }
}

#[cfg(test)]
mod tests;

pub(in crate::surface) fn resolve_resource_field_schema(
    definition: &ResourceDefinition,
    environment: &ClickFunctionEnvironment,
) -> Result<crate::kernel::ResourceFieldSchema, ClickError> {
    let fields = definition
        .fields()
        .iter()
        .map(|field| {
            let ty = match field.click_type() {
                ClickType::Proposition | ClickType::Function { .. } => {
                    return Err(ClickError::new(
                        "specification function fields are not supported",
                    ));
                }
                ClickType::Resource => {
                    return Err(ClickError::new(
                        "Resource values are supported as theorem parameters only",
                    ));
                }
                ClickType::Program(ty)
                | ClickType::CObjectPointer {
                    interface_type: ty, ..
                } => crate::kernel::ResourceFieldType::Program(ty.to_kernel_type()),
                ClickType::Algebraic(application) => crate::kernel::ResourceFieldType::Algebraic(
                    algebraic_kernel_type(environment, application).map_err(ClickError::new)?,
                ),
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
    crate::kernel::ResourceFieldSchema::new(fields).ok_or_else(|| {
        ClickError::new(format!(
            "invalid field schema for resource `{}`",
            definition.name()
        ))
    })
}

pub(in crate::surface) fn check_resource_field_schemas(
    file: &mut ClickFile,
) -> Result<(), ClickError> {
    let library_resources = super::super::validation::file_library(file)?.resource_definitions();
    if library_resources
        .iter()
        .chain(&file.resource_definitions)
        .all(ResourceDefinition::is_fieldless)
    {
        return Ok(());
    }
    let environment = ClickFunctionEnvironment::with_algebraic_types(
        &[],
        &super::super::validation::combined_algebraic_type_definitions(file)?,
    );
    let mut schemas = BTreeMap::new();
    for definition in library_resources
        .iter()
        .filter(|definition| !definition.is_fieldless())
    {
        let schema = resolve_resource_field_schema(definition, &environment)?;
        schemas.insert(definition.name().to_string(), schema);
    }
    for definition in &mut file.resource_definitions {
        if definition.is_fieldless() {
            continue;
        }
        let schema = resolve_resource_field_schema(definition, &environment)?;
        schemas.insert(definition.name().to_string(), schema.clone());
        definition.field_schema = Some(schema);
    }
    // Separate from the existing C/spec and composite-witness ranges. These
    // variables are collected from the entry resource state by the kernel's
    // fresh-variable allocator, so later execution cannot reuse their IDs.
    let mut next_field_variable = 9_000_000_000u64;
    for definition in &mut file.resource_definitions {
        for parameter in &mut definition.resource_parameters {
            let ResourceClause::Named { binding, resource } = parameter else {
                unreachable!()
            };
            let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                unreachable!()
            };
            binding.schema = Some(
                schemas
                    .get(name)
                    .ok_or_else(|| ClickError::new("resource parameter has no checked schema"))?
                    .clone(),
            );
        }
    }
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
    for function in file
        .function_blocks
        .iter_mut()
        .chain(
            file.contract_definitions
                .iter_mut()
                .map(|contract| &mut contract.function_block),
        )
        .chain(
            file.tactic_definitions
                .iter_mut()
                .map(TacticDefinition::function_block_mut),
        )
    {
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
            if matches!(
                name.as_str(),
                "mutex_live"
                    | "mutex_guard"
                    | "mutex_use"
                    | "authority"
                    | "publisher"
                    | "subscriber"
            ) {
                bindings.insert(binding.identity, binding.clone());
                continue;
            }
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
                        crate::kernel::ResourceFieldType::Program(ty) => AlgebraicValue::Program(
                            crate::kernel::symbolic_call_result(*ty, variable),
                        ),
                        crate::kernel::ResourceFieldType::Algebraic(ty) => {
                            AlgebraicValue::Algebraic(AlgebraicTerm {
                                algebraic_type: ty.clone(),
                                node: AlgebraicTermNode::Variable(variable),
                            })
                        }
                    }
                })
                .collect::<crate::kernel::ResourceFieldValues>();
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
                    if matches!(
                        name.as_str(),
                        "mutex_live"
                            | "mutex_guard"
                            | "mutex_use"
                            | "authority"
                            | "publisher"
                            | "subscriber"
                    ) {
                        // Primitive authority binders have no model-field
                        // schema, whether they are inputs or new outputs.
                        continue;
                    }
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

/// Registers one verified function's entry model fields, so a refusal can
/// spell them `old(c.rank)` instead of printing a kernel variable.
///
/// `check_resource_field_schemas` mints these variables once per sidecar, while
/// the registry they belong in is per verification — a field variable's meaning
/// is the verification's, because every other range restarts. So the selected
/// function registers its own binders here, beside the load-origin epoch that
/// starts for the same reason. One insert per field of each declared binder,
/// over the clause list the verification is about to walk anyway.
pub(in crate::surface) fn register_entry_model_fields(function: &FunctionBlock) {
    let bindings = function
        .requires
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::Resource(ResourceClause::Named { binding, resource }) => {
                Some((binding, resource))
            }
            _ => None,
        })
        .chain(
            function
                .ensures
                .iter()
                .filter_map(|ensure| match &ensure.ensure {
                    Ensure::Resource(ResourceClause::Named { binding, resource }) => {
                        Some((binding, resource))
                    }
                    _ => None,
                }),
        );
    for (binding, resource) in bindings {
        let (Some(schema), Some(fields)) = (&binding.schema, &binding.fields) else {
            continue;
        };
        for (field_index, ((field, _), value)) in
            schema.fields().iter().zip(fields.iter()).enumerate()
        {
            let Some(variable) = crate::kernel::algebraic_value_variable(value) else {
                continue;
            };
            crate::kernel::model_fields::register_model_field_variable(
                variable,
                crate::kernel::model_fields::ModelFieldOrigin {
                    identity: binding.identity,
                    field: std::sync::Arc::from(field.as_str()),
                    field_index,
                    minted_by: crate::kernel::model_fields::ModelMint::ContractEntry,
                },
            );
        }
        let spelling = if binding.name.starts_with('#') {
            let ResourceClause::Declared {
                name, arguments, ..
            } = resource.as_ref()
            else {
                continue;
            };
            crate::surface::diagnostics::describe_contract_expression(&ContractExpression::Call {
                name: name.clone(),
                arguments: arguments.clone(),
            })
        } else {
            binding.name.clone()
        };
        crate::kernel::model_fields::register_instance_spelling(binding.identity, &spelling);
    }
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
/// Match payloads are lexical values. Keep their declared carrier available
/// without asking the C-local environment to invent a slot for generated IDs.
fn bind_match_program_value(
    environment: &mut SpecElaborationContext,
    binding: &SurfaceBinder,
    value_type: ProgramType,
) {
    environment.integer_values.remove(binding);
    environment.algebraic_values.remove(binding);
    let value =
        SpecExpression::ProgramExpression(ProgramExpression::Variable(binding.kernel_name()));
    let value = if matches!(binding, SurfaceBinder::Generated(_)) {
        SpecExpression::Cast(Box::new(value), value_type)
    } else {
        value
    };
    environment.values.insert(binding, value);
}

fn contract_expression_is_algebraic(
    expression: &ContractExpression,
    functions: &ClickFunctionEnvironment,
    environment: &SpecElaborationContext,
    lexical_bindings: &mut Vec<(SurfaceBinder, bool)>,
) -> bool {
    if let Some(id) = expression.generated_binder() {
        return lexical_bindings
            .iter()
            .rev()
            .find_map(|(name, value)| (name == &SurfaceBinder::Generated(id)).then_some(*value))
            .unwrap_or_else(|| environment.algebraic_values.contains_key(&id));
    }

    match expression {
        ContractExpression::ResourceField(access) => {
            matches!(access.click_type, Some(ClickType::Algebraic(_)))
        }
        ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicVariable { .. } => true,
        ContractExpression::Binding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => lexical_bindings
            .iter()
            .rev()
            .find_map(|(binding, algebraic)| (binding == name).then_some(*algebraic))
            .unwrap_or_else(|| environment.algebraic_values.contains_key(name)),
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => contract_expression_is_algebraic(inner, functions, environment, lexical_bindings),
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            contract_expression_is_algebraic(then_branch, functions, environment, lexical_bindings)
                || contract_expression_is_algebraic(
                    else_branch,
                    functions,
                    environment,
                    lexical_bindings,
                )
        }
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
use crate::kernel::FloatClassification;
use crate::kernel::PredicateUnfolding;
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
    Vec<SpecProposition>,
    Vec<MemorySegment>,
    Vec<FunctionContractClaim>,
    bool,
    Vec<PredicateUnfolding>,
    Vec<crate::kernel::RankingComponent>,
);

/// Records each declared `Integer`-valued function's body with the kernel,
/// once per verification, so the kernel can decide whether it admits a
/// checked read summary (`docs/internals/fold-read-ranges.md`).
///
/// This registers program data only. The body is lowered by the same
/// annotation lowering an `unfold` of the function uses, with the parameters
/// left as the names the body refers to; the kernel validates it against its
/// own whitelist and declines anything outside it. A generic declaration, a
/// parameter that is not a C value, or a body this lowering refuses is simply
/// not recorded, and framing then has nothing to say about that function.
pub(in crate::surface) fn register_kernel_fold_read_definitions(
    spec_definitions: SpecDefinitions<'_>,
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) {
    for definition in spec_definitions.functions.definitions.values() {
        if !definition.type_parameters().is_empty()
            || definition.return_type() != &ClickType::Integer
        {
            continue;
        }
        let Some(parameters) = definition
            .parameters()
            .iter()
            .map(|parameter| match parameter.click_type() {
                ClickType::Program(interface_type)
                | ClickType::CObjectPointer { interface_type, .. } => Some((
                    parameter.name().to_string(),
                    interface_type.to_kernel_type(),
                )),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let entry_state = ExecutionState::new().with_population_creation_tracking();
        let mut lowerer = AnnotationLowerer {
            capture_referenced_names: None,
            source_bindings: None,
            structural_clauses: StructuralClauses::empty(),
            implicit_contract_mutable_segments: &[],
            loop_resources: BTreeMap::new(),
            inherits_resource_derived_frame: false,
            spec_definitions,
            entry_state: &entry_state,
            result_type: ProgramType::Int32,
            entry_values: ProgramValueBindings::new(),
            aggregate_parameters: BTreeSet::new(),
            program_parameter_types: BTreeMap::new(),
            local_type_state: None,
            pointer_element_types: definition
                .parameters()
                .iter()
                .filter_map(|parameter| {
                    Some((
                        parameter.name().to_string(),
                        click_array_element_type(parameter.click_type().interface_type()?)?,
                    ))
                })
                .collect(),
            parameter_pointer_element_widths: click_parameter_pointer_element_widths_with_layouts(
                definition.parameters(),
                struct_layouts,
            ),
            quantified_values: BinderMap::new(),
            algebraic_variables: BinderMap::new(),
            algebraic_types: BTreeMap::new(),
            loop_index: 0,
            statement_index: 0,
            next_quantifier_variable: 3_200_000,
            branch_join_target: None,
            retained_states: None,
            loop_records: None,
        };
        let Some(body) = definition.body() else {
            continue;
        };
        let Ok(body) =
            lowerer.lower_contract_integer_to_spec(body, &SpecElaborationContext::default())
        else {
            continue;
        };
        crate::kernel::register_fold_read_definition(crate::kernel::FoldReadDefinition::new(
            definition.name(),
            parameters,
            body,
        ));
    }
}

pub(in crate::surface) fn lower_composite_resource_condition(
    definition: &ResourceDefinition,
    spec_definitions: SpecDefinitions<'_>,
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> Result<Option<SpecProposition>, ClickError> {
    let Some(condition) = definition
        .composite_body()
        .expect("only composite definitions have conditions")
        .condition()
    else {
        return Ok(None);
    };
    let entry_state = ExecutionState::new().with_population_creation_tracking();
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: StructuralClauses::empty(),
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        spec_definitions,
        entry_state: &entry_state,
        result_type: ProgramType::Int32,
        entry_values: ProgramValueBindings::new(),
        aggregate_parameters: BTreeSet::new(),
        program_parameter_types: BTreeMap::new(),
        local_type_state: None,
        pointer_element_types: definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: click_parameter_pointer_element_widths_with_layouts(
            definition.parameters(),
            struct_layouts,
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
        branch_join_target: None,
        retained_states: None,
        loop_records: None,
    };
    let all_predicates = spec_definitions
        .predicates
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let condition = unfold_click_predicates_in_proposition_with_active(
        spec_definitions.predicates,
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

pub(in crate::surface) struct LoweredResourceBody {
    pub facts: Vec<SpecProposition>,
    pub fact_source_indices: Vec<usize>,
    pub children: Vec<crate::kernel::ResourceChildSpec>,
}

pub(in crate::surface) fn lower_composite_resource_body(
    definition: &ResourceDefinition,
    spec_definitions: SpecDefinitions<'_>,
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> Result<LoweredResourceBody, ClickError> {
    lower_composite_resource_body_with_bindings(
        definition,
        spec_definitions,
        &[],
        &BTreeMap::new(),
        struct_layouts,
    )
}

pub(in crate::surface) fn lower_composite_resource_body_with_bindings(
    definition: &ResourceDefinition,
    spec_definitions: SpecDefinitions<'_>,
    bindings: &[(String, ClickType)],
    integer_binding_variables: &BTreeMap<String, crate::kernel::Variable>,
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> Result<LoweredResourceBody, ClickError> {
    let body = definition
        .composite_body()
        .expect("only composite definitions have logical facts");
    let entry_state = ExecutionState::new().with_population_creation_tracking();
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: StructuralClauses::empty(),
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        spec_definitions,
        entry_state: &entry_state,
        result_type: ProgramType::Int32,
        entry_values: ProgramValueBindings::new(),
        aggregate_parameters: BTreeSet::new(),
        program_parameter_types: BTreeMap::new(),
        local_type_state: None,
        pointer_element_types: definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: click_parameter_pointer_element_widths_with_layouts(
            definition.parameters(),
            struct_layouts,
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
        branch_join_target: None,
        retained_states: None,
        loop_records: None,
    };
    let all_predicates = spec_definitions
        .predicates
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let mut facts = Vec::new();
    let mut fact_source_indices = Vec::new();
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
                    algebraic_type: algebraic_kernel_type(spec_definitions.functions, application)
                        .map_err(ClickError::new)?,
                    node: SpecAlgebraicExpressionNode::Binding(name.clone().into()),
                },
            );
        }
    }
    for (source_index, fact) in body.facts().iter().enumerate() {
        let unfolded = unfold_click_predicates_in_proposition_with_active(
            spec_definitions.predicates,
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
            fact_source_indices.push(source_index);
        }
        facts.push(
            lowerer
                .click_proposition_to_spec_proposition(&unfolded, &environment)
                .map_err(ClickError::new)?,
        );
        fact_source_indices.push(source_index);
    }
    let children = body
        .children
        .iter()
        .map(|child| {
            Ok(crate::kernel::ResourceChildSpec {
                name: child.name.clone(),
                resource: child.resource.clone(),
                binding: child.identity,
                field_bindings: child.field_bindings.clone(),
                arguments: child
                    .arguments
                    .iter()
                    .map(|argument| {
                        // Keep ordinary C argument evaluation on its existing checked path.
                        match resource_argument_to_program_expression(argument) {
                            Ok(expression) => Ok(SpecExpression::ProgramExpression(expression)),
                            Err(_) => lowerer
                                .lower_contract_expression_to_spec(argument, &environment)
                                .map_err(ClickError::new),
                        }
                    })
                    .collect::<Result<_, _>>()?,
            })
        })
        .collect::<Result<_, ClickError>>()?;
    Ok(LoweredResourceBody {
        facts,
        fact_source_indices,
        children,
    })
}

pub(in crate::surface) fn annotated_function(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    entry_state: &ExecutionState,
    arguments: &[ProgramExpression],
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
) -> Result<ProgramFunction, ClickError> {
    annotated_function_with_assumptions(
        function_block,
        parsed_function,
        entry_state,
        arguments,
        spec_definitions,
        resource_environment,
        None,
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
    pub(in crate::surface) checked_entry_state: Option<&'a ExecutionState>,
}

pub(in crate::surface) fn annotated_function_with_assumptions(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    entry_state: &ExecutionState,
    arguments: &[ProgramExpression],
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    frame_entry: Option<ResourceFrameEntry<'_>>,
    pointer_element_types: Option<&BTreeMap<String, ProgramType>>,
) -> Result<ProgramFunction, ClickError> {
    annotate_function(
        function_block,
        parsed_function,
        entry_state,
        arguments,
        spec_definitions,
        resource_environment,
        frame_entry,
        pointer_element_types,
        false,
    )
    .map(|(function, _)| function)
}

/// A function annotated for a `loop` tactic at one of its loops, with what
/// annotating it again for the next loop needs to lower that loop alone
/// ([`annotated_loop_function_extending`]).
#[derive(Clone)]
pub(in crate::surface) struct LoopAnnotation {
    function: ProgramFunction,
    /// The loop this annotation was made for.
    loop_index: usize,
    /// The quantifier counter once that loop was lowered, and whether the
    /// walk's scoped bindings were empty then.
    quantifiers_after: u64,
    bindings_empty_after: bool,
    shape: std::sync::Arc<LoopAnnotationShape>,
    /// The annotated loop as `kernel_loop_by_index` finds it in `function`,
    /// when lowering it alone already holds it.
    current_loop: Option<ProgramStatement>,
    /// Where each loop of `function`'s body sits, once a later annotation
    /// asked ([`KernelLoopPaths`]).
    kernel_loop_paths: std::sync::OnceLock<std::sync::Arc<KernelLoopPaths>>,
}

/// One step of the path from a kernel body's root to a loop: the statement
/// of a sequence at an index, or an arm of an `if`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum KernelLoopStep {
    Statement(usize),
    Then,
    Else,
}

/// For each loop index `kernel_loop_by_index` numbers in a body, the path to
/// that loop when [`kernel_loop_replaced`] can put a lowered loop in its place
/// (it is reached through sequences and `if` arms alone), from one walk of
/// the body. Putting a loop in place then follows the path: its length is
/// the nesting depth, and each sequence on it replaces one statement in
/// logarithmic time, so the statements before the loop are not walked or
/// rebuilt.
///
/// The paths stay those of a body in which a loop at one of them was
/// replaced by a statement with the same number of loops: every other
/// statement keeps its place and every loop its number.
struct KernelLoopPaths {
    paths: Vec<Option<Vec<KernelLoopStep>>>,
}

impl KernelLoopPaths {
    fn of(body: &ProgramStatement) -> Self {
        fn walk(
            statement: &ProgramStatement,
            path: &mut Vec<KernelLoopStep>,
            paths: &mut Vec<Option<Vec<KernelLoopStep>>>,
        ) {
            match statement {
                ProgramStatement::Loop {
                    test: loop_test,
                    update,
                    body,
                    ..
                } => {
                    let test = loop_test.source_region();
                    paths.push(Some(path.clone()));
                    // A loop inside another is not one a walk lowers alone.
                    paths.extend(std::iter::repeat_n(
                        None,
                        count_kernel_loops(body)
                            + test
                                .as_ref()
                                .map_or(0, |test| count_kernel_loops(&test.statement))
                            + update
                                .as_ref()
                                .map_or(0, |update| count_kernel_loops(update)),
                    ));
                }
                ProgramStatement::Seq(statements) => {
                    for (index, statement) in statements.iter().enumerate() {
                        path.push(KernelLoopStep::Statement(index));
                        walk(statement, path, paths);
                        path.pop();
                    }
                }
                ProgramStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    path.push(KernelLoopStep::Then);
                    walk(then_branch, path, paths);
                    path.pop();
                    path.push(KernelLoopStep::Else);
                    walk(else_branch, path, paths);
                    path.pop();
                }
                // A loop under any other statement is not one a walk lowers
                // alone.
                statement => {
                    paths.extend(std::iter::repeat_n(None, count_kernel_loops(statement)));
                }
            }
        }
        let mut paths = Vec::new();
        walk(body, &mut Vec::new(), &mut paths);
        Self { paths }
    }

    /// `body`, the body these paths were read from, with the loop numbered
    /// `target` replaced by `replacement`: what [`kernel_loop_replaced`]
    /// returns, without walking the statements before the loop.
    fn replaced(
        &self,
        body: &ProgramStatement,
        target: usize,
        replacement: &ProgramStatement,
    ) -> Option<ProgramStatement> {
        fn at(
            statement: &ProgramStatement,
            path: &[KernelLoopStep],
            replacement: &ProgramStatement,
        ) -> Option<ProgramStatement> {
            #[cfg(test)]
            KERNEL_LOOP_REPLACEMENT_STEPS.with(|count| count.set(count.get() + 1));
            let Some((step, path)) = path.split_first() else {
                return matches!(statement, ProgramStatement::Loop { .. })
                    .then(|| replacement.clone());
            };
            match (step, statement) {
                (KernelLoopStep::Statement(index), ProgramStatement::Seq(statements)) => {
                    let replaced = at(statements.get(*index)?, path, replacement)?;
                    Some(ProgramStatement::Seq(
                        statements.with_statement(*index, std::sync::Arc::new(replaced)),
                    ))
                }
                (
                    KernelLoopStep::Then,
                    ProgramStatement::If {
                        condition,
                        then_branch,
                        else_branch,
                    },
                ) => Some(ProgramStatement::If {
                    condition: condition.clone(),
                    then_branch: Box::new(at(then_branch, path, replacement)?),
                    else_branch: else_branch.clone(),
                }),
                (
                    KernelLoopStep::Else,
                    ProgramStatement::If {
                        condition,
                        then_branch,
                        else_branch,
                    },
                ) => Some(ProgramStatement::If {
                    condition: condition.clone(),
                    then_branch: then_branch.clone(),
                    else_branch: Box::new(at(else_branch, path, replacement)?),
                }),
                _ => None,
            }
        }
        at(body, self.paths.get(target)?.as_ref()?, replacement)
    }

    /// The loop at `target`'s path in `body`, when there is one.
    fn loop_at<'a>(
        &self,
        body: &'a ProgramStatement,
        target: usize,
    ) -> Option<&'a ProgramStatement> {
        let mut statement = body;
        for step in self.paths.get(target)?.as_ref()? {
            statement = match (step, statement) {
                (KernelLoopStep::Statement(index), ProgramStatement::Seq(statements)) => {
                    statements.get(*index)?
                }
                (KernelLoopStep::Then, ProgramStatement::If { then_branch, .. }) => then_branch,
                (KernelLoopStep::Else, ProgramStatement::If { else_branch, .. }) => else_branch,
                _ => return None,
            };
        }
        matches!(statement, ProgramStatement::Loop { .. }).then_some(statement)
    }
}

#[cfg(test)]
thread_local! {
    static KERNEL_LOOP_REPLACEMENT_STEPS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The statements putting lowered loops in place (`KernelLoopPaths::replaced`)
/// visited on this thread so far.
#[cfg(test)]
pub(in crate::surface) fn kernel_loop_replacement_steps() -> usize {
    KERNEL_LOOP_REPLACEMENT_STEPS.with(std::cell::Cell::get)
}

/// The parts of a whole-function annotation that do not depend on its loop
/// clauses: what the walk saw at each loop, and the contract's lowered
/// write footprint a loop without a resource clause inherits.
struct LoopAnnotationShape {
    records: Vec<LoopLoweringRecord>,
    contract_mutable: Vec<MemorySegment>,
    resource_derived_mutable_frame: bool,
    /// Whether one loop can be lowered alone at all: the walk lowered the
    /// function's own body, numbering every loop the kernel body holds, and
    /// no loop declares resources (which are lowered for every loop before
    /// the body) or wraps the whole body as a natural control loop.
    loops_lower_alone: bool,
    /// What [`c_loop_by_index`] finds at each loop index of the function's
    /// body, from one walk, so lowering one loop alone does not walk the
    /// statements before it.
    c_loops: std::sync::OnceLock<Vec<Option<syntax::CStatement>>>,
}

impl LoopAnnotationShape {
    /// [`c_loop_by_index`] of `body` at `target`. `body` is the body of the
    /// function this shape was recorded from: every call passes it.
    fn c_loop(&self, body: &syntax::CStatement, target: usize) -> Option<&syntax::CStatement> {
        self.c_loops
            .get_or_init(|| c_loops_by_index(body))
            .get(target)?
            .as_ref()
    }
}

impl LoopAnnotation {
    pub(in crate::surface) fn function(&self) -> &ProgramFunction {
        &self.function
    }

    /// What `kernel_loop_by_index` finds at this annotation's loop in
    /// `function`, if it is already known.
    pub(in crate::surface) fn current_loop(&self) -> Option<&ProgramStatement> {
        self.current_loop.as_ref()
    }
}

/// The function annotated for the `loop` tactic at `loop_index`: what
/// [`annotated_function_with_assumptions`] lowers, with the walk's records.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn annotated_loop_function(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    entry_state: &ExecutionState,
    arguments: &[ProgramExpression],
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    frame_entry: Option<ResourceFrameEntry<'_>>,
    pointer_element_types: Option<&BTreeMap<String, ProgramType>>,
    loop_index: usize,
) -> Result<LoopAnnotation, ClickError> {
    count_annotation_walks(1);
    let (function, shape) = annotate_function(
        function_block,
        parsed_function,
        entry_state,
        arguments,
        spec_definitions,
        resource_environment,
        frame_entry,
        pointer_element_types,
        true,
    )?;
    let shape = shape.expect("a recording annotation returns its shape");
    let record = shape.records.get(loop_index).copied();
    Ok(LoopAnnotation {
        function,
        loop_index,
        quantifiers_after: record.map_or(0, |record| record.quantifiers_after),
        bindings_empty_after: record.is_some_and(|record| record.bindings_empty_after),
        shape: std::sync::Arc::new(shape),
        current_loop: None,
        kernel_loop_paths: std::sync::OnceLock::new(),
    })
}

/// The function annotated for the `loop` tactic at `loop_index`, made from
/// `previous`, the annotation for the loop just before it, by lowering only
/// this loop and putting it in place of that annotation's copy of it.
///
/// The caller guarantees that `function_block` differs from the block
/// `previous` was annotated from only in this loop's clause, and that every
/// other input is the one `previous` was made from. Then a whole-function
/// walk would lower every other loop as `previous` holds it: the loops
/// before this one see the same clauses and walk state, and the loops after
/// it have no clause in either, so they consume no walk state. This loop's
/// walk state is the one `previous` recorded once its own loop was lowered,
/// since only statements without loops lie between them; its statement
/// counter is positional. The result is therefore the whole-function
/// annotation. `None` when that argument does not apply: another loop in
/// between, a loop with nested loops or declared resources, a `for` loop,
/// a natural control loop, or clauses carrying proof scopes.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn annotated_loop_function_extending(
    previous: &LoopAnnotation,
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    entry_state: &ExecutionState,
    arguments: &[ProgramExpression],
    spec_definitions: SpecDefinitions<'_>,
    frame_entry: Option<ResourceFrameEntry<'_>>,
    pointer_element_types: Option<&BTreeMap<String, ProgramType>>,
    loop_index: usize,
) -> Result<Option<LoopAnnotation>, ClickError> {
    let shape = &previous.shape;
    let (Some(earlier), Some(record)) = (
        shape.records.get(previous.loop_index),
        shape.records.get(loop_index),
    ) else {
        return Ok(None);
    };
    if !shape.loops_lower_alone
        || loop_index != previous.loop_index + 1
        || !earlier.lowered_alone
        || !record.lowered_alone
        || !previous.bindings_empty_after
        || function_block
            .structural_clauses()
            .any_scoped_or_resourced()
    {
        return Ok(None);
    }
    let parsed_function =
        &*crate::surface::verification::witnessed_function(parsed_function, function_block);
    let Some(loop_statement) = shape.c_loop(parsed_function.body(), loop_index) else {
        return Ok(None);
    };
    let implicit_contract_mutable_segments = if shape.resource_derived_mutable_frame {
        &[]
    } else {
        shape.contract_mutable.as_slice()
    };
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: function_block.structural_clauses(),
        implicit_contract_mutable_segments,
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: shape.resource_derived_mutable_frame,
        spec_definitions,
        entry_state: frame_entry
            .and_then(|frame_entry| frame_entry.checked_entry_state)
            .unwrap_or(entry_state),
        result_type: if parsed_function.return_struct_name().is_some() {
            ProgramType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        entry_values: parameter_values(ParameterBinding::new(
            parsed_function.parameters(),
            arguments,
        ))?,
        aggregate_parameters: parsed_function
            .parameters()
            .iter()
            .filter(|p| p.is_struct_value())
            .map(|p| p.name().to_string())
            .collect(),
        program_parameter_types: parsed_function
            .parameters()
            .iter()
            .map(|parameter| {
                (
                    parameter.name().to_string(),
                    parameter.interface_type().to_kernel_type(),
                )
            })
            .collect(),
        local_type_state: None,
        pointer_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                if parameter.is_struct_value() {
                    return Some((parameter.name().to_string(), ProgramType::Int32));
                }
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index,
        statement_index: record.statement_index,
        next_quantifier_variable: previous.quantifiers_after,
        branch_join_target: None,
        retained_states: None,
        loop_records: None,
    };
    match pointer_element_types {
        Some(types) => lowerer
            .pointer_element_types
            .extend(types.iter().map(|(name, element)| (name.clone(), *element))),
        None => return Ok(None),
    }
    let lowered = lowerer.lower_statement(loop_statement, parsed_function.control_targets())?;
    let quantifiers_after = lowerer.next_quantifier_variable;
    let bindings_empty_after =
        lowerer.quantified_values.is_empty() && lowerer.algebraic_variables.is_empty();
    let lowered = if previous.function.resource_derived_mutable_frame()
        && !function_block.is_external()
        && let Some(frame_entry) = frame_entry
    {
        // The frames are read off the function's entry clauses alone, so the
        // loop is given the ranges every other loop of `previous` holds.
        let checked_entry = match frame_entry.checked_entry_state {
            Some(state) => state.clone(),
            None => crate::kernel::program_function_entry_state(
                entry_state,
                &previous.function,
                arguments,
            )
            .ok_or_else(|| {
                ClickError::new(format!(
                    "could not construct the resource-derived loop entry for `{}`",
                    parsed_function.name()
                ))
            })?,
        };
        let mut budget = crate::kernel::ExecutionBudget::for_new_execution();
        match crate::kernel::establish_resource_derived_loop_frames(
            previous.function.clone().with_body(lowered),
            &checked_entry,
            &frame_entry.assumptions.clone().assume_entry_clause_spans(),
            &mut budget,
        ) {
            Ok(Ok(function)) => function.body().clone(),
            Ok(Err(message)) => {
                return Err(ClickError::new(format!(
                    "could not establish resource-derived loop frames for `{}`: {message}",
                    parsed_function.name()
                )));
            }
            Err(limit) => {
                return Err(ClickError::new(format!(
                    "resource-derived loop-frame establishment for `{}` stopped at {}",
                    limit.describe(),
                    parsed_function.name()
                )));
            }
        }
    } else {
        lowered
    };
    let paths = previous
        .kernel_loop_paths
        .get_or_init(|| std::sync::Arc::new(KernelLoopPaths::of(previous.function.body())));
    let Some(body) = paths.replaced(previous.function.body(), loop_index, &lowered) else {
        return Ok(None);
    };
    #[cfg(debug_assertions)]
    if loop_annotation_check_enabled() {
        crate::instrumentation::uncharged_debug_check(|| {
            assert!(
                kernel_loop_replaced(previous.function.body(), loop_index, &mut 0, &lowered)
                    .as_ref()
                    == Some(&body),
                "loop({loop_index}) was put in place where the walk would not put it"
            );
        });
    }
    // The paths still hold for `body` when the lowered loop holds as many
    // loops as the one it replaced.
    let kernel_loop_paths = std::sync::OnceLock::new();
    if paths
        .loop_at(previous.function.body(), loop_index)
        .is_some_and(|replaced| count_kernel_loops(replaced) == count_kernel_loops(&lowered))
    {
        let _ = kernel_loop_paths.set(paths.clone());
    }
    // `body` numbers every loop before `lowered` as `previous.function`
    // does, so a walk of `body` reaches `lowered` with `loop_index` loops
    // counted and finds this loop inside it.
    let mut next_loop_index = loop_index;
    let current_loop = kernel_loop_by_index(&lowered, loop_index, &mut next_loop_index).cloned();
    Ok(Some(LoopAnnotation {
        function: previous.function.clone().with_body(body),
        loop_index,
        quantifiers_after,
        bindings_empty_after,
        shape: previous.shape.clone(),
        current_loop,
        kernel_loop_paths,
    }))
}

/// The C loop node a whole-function walk gives loop index `target`, found
/// in that walk's order: `while`, `do` and `for` loops number themselves
/// before their bodies, and only sequences, loops and `if` arms are
/// descended, as `AnnotationLowerer::lower_statement` descends them.
/// [`c_loops_by_index`] answers every index from one walk; this is its
/// reference.
#[cfg(test)]
fn c_loop_by_index(statement: &syntax::CStatement, target: usize) -> Option<&syntax::CStatement> {
    fn find<'s>(
        statement: &'s syntax::CStatement,
        target: usize,
        next: &mut usize,
    ) -> Option<&'s syntax::CStatement> {
        match statement {
            syntax::CStatement::Seq(first, second) => {
                find(first, target, next).or_else(|| find(second, target, next))
            }
            syntax::CStatement::While { test, body, .. }
            | syntax::CStatement::DoWhile { test, body, .. }
            | syntax::CStatement::For { test, body, .. } => {
                let index = *next;
                *next += 1;
                if index == target {
                    Some(statement)
                } else {
                    find(body, target, next)
                        .or_else(|| test.as_ref().and_then(|test| find(test, target, next)))
                }
            }
            syntax::CStatement::If {
                then_branch,
                else_branch,
                ..
            } => find(then_branch, target, next).or_else(|| find(else_branch, target, next)),
            _ => None,
        }
    }
    let mut next = 0;
    let found = find(statement, target, &mut next)?;
    matches!(
        found,
        syntax::CStatement::While { .. } | syntax::CStatement::DoWhile { .. }
    )
    .then_some(found)
}

/// The kernel loop numbered `target` in `statement`, numbering each
/// `while` before its body, from `*next_loop_index`.
pub(in crate::surface) fn kernel_loop_by_index<'a>(
    statement: &'a ProgramStatement,
    target: usize,
    next_loop_index: &mut usize,
) -> Option<&'a ProgramStatement> {
    #[cfg(test)]
    LOOP_LOOKUP_NODES.with(|count| count.set(count.get() + 1));
    match statement {
        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            let loop_index = *next_loop_index;
            *next_loop_index += 1;
            if loop_index == target {
                Some(statement)
            } else {
                test.filter(|test| test.position == crate::kernel::LoopTestPosition::BeforeBody)
                    .and_then(|test| kernel_loop_by_index(&test.statement, target, next_loop_index))
                    .or_else(|| kernel_loop_by_index(body, target, next_loop_index))
                    .or_else(|| {
                        update.as_ref().and_then(|update| {
                            kernel_loop_by_index(update, target, next_loop_index)
                        })
                    })
                    .or_else(|| {
                        test.filter(|test| {
                            test.position == crate::kernel::LoopTestPosition::AfterBody
                        })
                        .and_then(|test| {
                            kernel_loop_by_index(&test.statement, target, next_loop_index)
                        })
                    })
            }
        }
        ProgramStatement::Seq(statements) => statements
            .iter()
            .find_map(|statement| kernel_loop_by_index(statement, target, next_loop_index)),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => kernel_loop_by_index(then_branch, target, next_loop_index)
            .or_else(|| kernel_loop_by_index(else_branch, target, next_loop_index)),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => kernel_loop_by_index(try_body, target, next_loop_index)
            .or_else(|| kernel_loop_by_index(handler, target, next_loop_index)),
        ProgramStatement::Switch { cases, .. } => cases
            .iter()
            .find_map(|case| kernel_loop_by_index(&case.body, target, next_loop_index)),
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. } => None,
        ProgramStatement::EndAutomaticLifetimes { .. } => None,
    }
}

#[cfg(test)]
thread_local! {
    static LOOP_LOOKUP_NODES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The statements loop lookups (`kernel_loop_by_index`, and the C loop
/// index) visited on this thread so far.
#[cfg(test)]
pub(in crate::surface) fn loop_lookup_nodes() -> usize {
    LOOP_LOOKUP_NODES.with(std::cell::Cell::get)
}

/// Every loop index's [`c_loop_by_index`] answer for `statement`, from
/// one walk in the same order.
fn c_loops_by_index(statement: &syntax::CStatement) -> Vec<Option<syntax::CStatement>> {
    fn walk(statement: &syntax::CStatement, found: &mut Vec<Option<syntax::CStatement>>) {
        #[cfg(test)]
        LOOP_LOOKUP_NODES.with(|count| count.set(count.get() + 1));
        match statement {
            syntax::CStatement::Seq(first, second) => {
                walk(first, found);
                walk(second, found);
            }
            syntax::CStatement::While { test, body, .. }
            | syntax::CStatement::DoWhile { test, body, .. } => {
                found.push(Some(statement.clone()));
                walk(body, found);
                if let Some(test) = test {
                    walk(test, found);
                }
            }
            syntax::CStatement::For { test, body, .. } => {
                found.push(None);
                walk(body, found);
                if let Some(test) = test {
                    walk(test, found);
                }
            }
            syntax::CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                walk(then_branch, found);
                walk(else_branch, found);
            }
            _ => {}
        }
    }
    let mut found = Vec::new();
    walk(statement, &mut found);
    found
}

/// `statement` with the loop `kernel_loop_by_index` finds at `target`
/// replaced by `replacement`: the statements on the way to it are rebuilt,
/// every other part is shared. It walks every statement before the loop;
/// [`KernelLoopPaths::replaced`] answers the same without, and this is its
/// reference.
#[cfg(any(test, debug_assertions))]
fn kernel_loop_replaced(
    statement: &ProgramStatement,
    target: usize,
    next: &mut usize,
    replacement: &ProgramStatement,
) -> Option<ProgramStatement> {
    match statement {
        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            let index = *next;
            *next += 1;
            if index == target {
                return Some(replacement.clone());
            }
            // A loop inside another is not one a walk lowers alone.
            *next += count_kernel_loops(body)
                + test
                    .as_ref()
                    .map_or(0, |test| count_kernel_loops(&test.statement))
                + update
                    .as_ref()
                    .map_or(0, |update| count_kernel_loops(update));
            None
        }
        ProgramStatement::Seq(statements) => {
            for (index, statement) in statements.iter().enumerate() {
                if let Some(replaced) = kernel_loop_replaced(statement, target, next, replacement) {
                    return Some(ProgramStatement::Seq(
                        statements.with_statement(index, std::sync::Arc::new(replaced)),
                    ));
                }
            }
            None
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            if let Some(then_branch) = kernel_loop_replaced(then_branch, target, next, replacement)
            {
                return Some(ProgramStatement::If {
                    condition: condition.clone(),
                    then_branch: Box::new(then_branch),
                    else_branch: else_branch.clone(),
                });
            }
            let else_branch = kernel_loop_replaced(else_branch, target, next, replacement)?;
            Some(ProgramStatement::If {
                condition: condition.clone(),
                then_branch: then_branch.clone(),
                else_branch: Box::new(else_branch),
            })
        }
        // A loop under any other statement is not one a walk lowers alone.
        statement => {
            *next += count_kernel_loops(statement);
            None
        }
    }
}

/// The loops `kernel_loop_by_index` numbers in `statement`.
fn count_kernel_loops(statement: &ProgramStatement) -> usize {
    match statement {
        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            1 + count_kernel_loops(body)
                + test
                    .as_ref()
                    .map_or(0, |test| count_kernel_loops(&test.statement))
                + update
                    .as_ref()
                    .map_or(0, |update| count_kernel_loops(update))
        }
        ProgramStatement::Seq(statements) => statements
            .iter()
            .map(|statement| count_kernel_loops(statement))
            .sum(),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => count_kernel_loops(then_branch) + count_kernel_loops(else_branch),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => count_kernel_loops(try_body) + count_kernel_loops(handler),
        ProgramStatement::Switch { cases, .. } => cases
            .iter()
            .map(|case| count_kernel_loops(&case.body))
            .sum(),
        _ => 0,
    }
}

#[allow(clippy::too_many_arguments)]
fn annotate_function(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    entry_state: &ExecutionState,
    arguments: &[ProgramExpression],
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
    frame_entry: Option<ResourceFrameEntry<'_>>,
    pointer_element_types: Option<&BTreeMap<String, ProgramType>>,
    record_loops: bool,
) -> Result<(ProgramFunction, Option<LoopAnnotationShape>), ClickError> {
    // A frontier loop clause carries the proof scope it was written under;
    // lowering reads every clause through that scope.
    let resolved_block = resolved_function_block(function_block)?;
    let function_block: &FunctionBlock = &resolved_block;
    let parsed_function =
        &*crate::surface::verification::witnessed_function(parsed_function, function_block);
    let (resource_requires, resource_ensures) = function_resource_summary(
        function_block,
        parsed_function,
        spec_definitions,
        resource_environment,
    )?;
    let resource_constructors = function_resource_constructors(function_block)?;
    let (
        contract_requires,
        contract_requirement_sources,
        contract_ensures,
        exceptional_ensures,
        contract_mutable,
        contract_claims,
        opaque_contract_supported,
        predicate_unfoldings,
        recursion_measure,
    ) = function_contract_summary(
        function_block,
        parsed_function,
        spec_definitions,
        resource_environment,
    )?;
    // Startup already provides the memory frame for main. Its stream
    // resource carries a logical history without transferring C memory.
    let resource_derived_mutable_frame = parsed_function.program_entry_state.is_none()
        && !function_block.is_tactic_procedure()
        && (construction_result_layout(parsed_function).is_some()
            || function_block
                .requires()
                .iter()
                .any(|requirement| matches!(requirement, Requirement::Resource(_))));
    // A resource-derived function's write footprint is never lowered from
    // source: the kernel projects it from the checked resource transition,
    // and a loop inherits it as validated ranges installed at function
    // entry. Only a function with explicit startup segments hands a loop a
    // segment list here.
    let implicit_contract_mutable_segments = if resource_derived_mutable_frame {
        &[]
    } else {
        contract_mutable.as_slice()
    };
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: function_block.structural_clauses(),
        implicit_contract_mutable_segments,
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: resource_derived_mutable_frame,
        spec_definitions,
        // `old(...)` names the function entry. A frontier loop is annotated
        // from the proof's execution start, which a proof that unfolds a
        // resource before its first step has already moved past: the unfold
        // names the body's cells in a new state. Lowering `old` there
        // would give the loop's entry-state reads a state the proof's
        // own `old(...)` and `at(function.entry, ...)` never name, so the
        // checked function entry is used when the proof recorded one.
        entry_state: frame_entry
            .and_then(|frame_entry| frame_entry.checked_entry_state)
            .unwrap_or(entry_state),
        result_type: if parsed_function.return_struct_name().is_some() {
            ProgramType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        entry_values: parameter_values(ParameterBinding::new(
            parsed_function.parameters(),
            arguments,
        ))?,
        aggregate_parameters: parsed_function
            .parameters()
            .iter()
            .filter(|p| p.is_struct_value())
            .map(|p| p.name().to_string())
            .collect(),
        program_parameter_types: parsed_function
            .parameters()
            .iter()
            .map(|parameter| {
                (
                    parameter.name().to_string(),
                    parameter.interface_type().to_kernel_type(),
                )
            })
            .collect(),
        local_type_state: None,
        pointer_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                if parameter.is_struct_value() {
                    return Some((parameter.name().to_string(), ProgramType::Int32));
                }
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_000_000,
        branch_join_target: None,
        retained_states: None,
        loop_records: record_loops.then(Vec::new),
    };
    let parsed_kernel_function = parsed_function.to_kernel_function();
    match pointer_element_types {
        Some(types) => lowerer
            .pointer_element_types
            .extend(types.iter().map(|(name, element)| (name.clone(), *element))),
        None => collect_local_pointer_element_types(
            parsed_kernel_function.body(),
            &mut lowerer.pointer_element_types,
        ),
    }
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
    let prelowered = parsed_function.prelowered_kernel_function().is_some();
    let body = if prelowered {
        lowerer.lower_kernel_statement(parsed_kernel_function.body())?
    } else {
        lowerer.lower_statement(parsed_function.body(), parsed_function.control_targets())?
    };
    let natural_source = parsed_function.natural_control_loop();
    let natural_control_loop = natural_source.is_some();
    let body = if let Some((backedge_target, natural_exit_target, _)) = natural_source
        && function_block.structural_clauses().for_loop(0).is_some()
    {
        let invariant_checks = lowerer.loop_invariant_checks(0)?;
        let effect_checks = lowerer.loop_frame_checks(0)?;
        let resource_specs = lowerer.loop_resource_specs(0);
        let (ranking_measures, structural_measure) = lowerer.loop_measure_clauses(0, None)?;
        let mut loop_body = crate::kernel::program_while_with_invariant_and_effect_checks(
            crate::kernel::program_expression::int32_literal(1),
            Vec::new(),
            invariant_checks,
            effect_checks,
            body,
        )
        .with_loop_resource_specs(resource_specs)
        .with_loop_ranking_measures(ranking_measures)
        .with_loop_structural_measure(structural_measure)
        .with_backedge_target(backedge_target);
        if let Some(target) = natural_exit_target {
            loop_body = loop_body.with_natural_exit_target(target);
        }
        loop_body
    } else {
        body
    };
    let no_loop_resources = lowerer.loop_resources.is_empty();
    let recorded = lowerer
        .loop_records
        .take()
        .map(|records| (records, contract_mutable.clone()));
    let source_body = parsed_kernel_function.body().clone();
    let mut function = program_function(
        if parsed_function.return_struct_name().is_some() {
            ProgramType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        parsed_function.name().to_string(),
        parsed_function
            .parameters()
            .iter()
            .map(crate::languages::interface::ImportedParameter::to_kernel_parameter)
            .collect(),
        body,
    )
    .with_return_pointee_constant(parsed_function.return_pointee_is_constant())
    .with_return_pointee_class(parsed_function.return_pointee_class())
    .with_source_body(source_body)
    .with_natural_loop_source(natural_source.map(|(target, exit, _)| (target, exit)))
    .with_control_targets_from(&parsed_kernel_function);
    if parsed_kernel_function.is_program_entry() {
        function = function.with_program_entry();
    }
    if let Some(struct_name) = parsed_function.return_struct_name() {
        let layout = parsed_function
            .structs()
            .get(struct_name)
            .expect("struct return has a parsed layout")
            .to_kernel_aggregate_layout();
        function = match parsed_kernel_function
            .contract_interface()
            .aggregate_return_mode()
        {
            crate::kernel::AggregateReturnMode::Copy => {
                function.with_return_aggregate_layout(layout)
            }
            crate::kernel::AggregateReturnMode::Construction => {
                function.with_construction_return(layout)
            }
        };
    }
    if let Some((index, layout)) = parsed_kernel_function
        .contract_interface()
        .construction_parameter()
    {
        function = function.with_construction_parameter(index, layout.clone());
    }
    let mut function = function
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
                .map(syntax::CStringLiteral::to_kernel)
                .collect(),
        )
        .with_resource_summary(resource_requires, resource_ensures)
        .with_resource_constructors(resource_constructors)
        .with_composite_resource_definitions(composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?)
        .with_ordinary_abstract_families(ordinary_abstract_families(resource_environment))
        .with_predicate_unfoldings(predicate_unfoldings)
        .with_contract(
            contract_requires,
            contract_ensures,
            contract_mutable,
            contract_claims,
            opaque_contract_supported,
        )
        .with_contract_requirement_sources(contract_requirement_sources);
    // The peers travel with the measure: they are what the anchor
    // ranks calls to, and a function without an expression measure ranks
    // none.
    let recursion_binder = match function_block.decreases() {
        Some(FunctionDecrease::Binder(binder)) => Some(binder.clone()),
        _ => None,
    };
    let recursion_resource =
        crate::surface::verification::function_recursion_resource_requirement(function_block)?;
    if !recursion_measure.is_empty() || recursion_binder.is_some() || recursion_resource.is_some() {
        function = function.with_recursion_peers(function_block.recursion_peers().to_vec());
    }
    function = function
        .with_recursion_binder(recursion_binder)
        .with_recursion_resource(recursion_resource);
    function = function.with_recursion_measure(recursion_measure);
    if let Some(exceptional_type) = function_block.signature().exceptional_type() {
        function = function
            .with_exceptional_outcome(exceptional_type.to_kernel_type())
            .with_exceptional_ensures(exceptional_ensures);
    }
    let function = function
        .with_trailing_value_parameters(function_block.witness_count())
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{}` has more contract value parameters than parameters",
                function_block.signature().name()
            ))
        })?;
    let function = if resource_derived_mutable_frame {
        let function = function.with_resource_derived_mutable_frame();
        if !function_block.is_external()
            && let Some(frame_entry) = frame_entry
        {
            let checked_entry = match frame_entry.checked_entry_state {
                Some(state) => state.clone(),
                None => {
                    crate::kernel::program_function_entry_state(entry_state, &function, arguments)
                        .ok_or_else(|| {
                        ClickError::new(format!(
                            "could not construct the resource-derived loop entry for `{}`",
                            parsed_function.name()
                        ))
                    })?
                }
            };
            let mut budget = crate::kernel::ExecutionBudget::for_new_execution();
            // The frames are read off the function's own entry clauses.
            match crate::kernel::establish_resource_derived_loop_frames(
                function,
                &checked_entry,
                &frame_entry.assumptions.clone().assume_entry_clause_spans(),
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
                        "resource-derived loop-frame establishment for `{}` stopped at {}",
                        limit.describe(),
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
    let shape = recorded.map(|(records, contract_mutable)| LoopAnnotationShape {
        loops_lower_alone: !natural_control_loop
            && !prelowered
            && no_loop_resources
            && count_kernel_loops(function.body()) == records.len(),
        records,
        contract_mutable,
        resource_derived_mutable_frame,
        c_loops: std::sync::OnceLock::new(),
    });
    Ok((function, shape))
}

/// Lowers one `branch ensuring` fact as a state-parametric kernel
/// proposition. Unlike fixed-state proof lowering, this keeps C bindings as
/// expressions so the kernel can check the same interface against both
/// concrete arm states and the abstract successor state.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn lower_branch_interface_fact(
    proposition: &ClickProposition,
    parsed_function: &crate::languages::interface::ImportedFunction,
    entry_state: &ExecutionState,
    current_state: &ExecutionState,
    branch_join_target: &ProgramPointRef,
    retained_states: &RecordedStates,
    arguments: &[ProgramExpression],
    spec_definitions: SpecDefinitions<'_>,
) -> Result<SpecProposition, ClickError> {
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: StructuralClauses::empty(),
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        spec_definitions,
        entry_state,
        result_type: if parsed_function.return_struct_name().is_some() {
            ProgramType::UInt8Pointer
        } else {
            parsed_function.return_type().to_kernel_type()
        },
        entry_values: parameter_values(ParameterBinding::new(
            parsed_function.parameters(),
            arguments,
        ))?,
        aggregate_parameters: parsed_function
            .parameters()
            .iter()
            .filter(|p| p.is_struct_value())
            .map(|p| p.name().to_string())
            .collect(),
        program_parameter_types: parsed_function
            .parameters()
            .iter()
            .map(|parameter| {
                (
                    parameter.name().to_string(),
                    parameter.interface_type().to_kernel_type(),
                )
            })
            .collect(),
        local_type_state: Some(current_state),
        pointer_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 2_000_000,
        branch_join_target: Some(branch_join_target),
        retained_states: Some(retained_states),
        loop_records: None,
    };
    lowerer
        .click_proposition_to_spec_proposition(proposition, &SpecElaborationContext::default())
        .map_err(ClickError::new)
}

/// The elaborator and context of a fixed-state proof: `old(...)` names the
/// function entry, a predicate call stays a predicate, recorded states
/// are fixed states, and the proof's current locals and `result` are fixed
/// values. `array_element_types` names the array parameters and proof-local
/// array bindings in scope; `opaque_click_functions` names the calls the
/// proof unfolds itself.
#[allow(clippy::too_many_arguments)]
fn fixed_state_elaboration<'a>(
    array_element_types: BTreeMap<String, ProgramType>,
    bound_array_memories: BTreeMap<String, SpecPoint>,
    entry_state: &'a ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    result: Option<&ProgramValue>,
    retained_states: &'a RecordedStates,
    spec_definitions: SpecDefinitions<'a>,
    _opaque_click_functions: BTreeSet<String>,
    parameter_pointer_element_widths: BTreeMap<String, u32>,
) -> (AnnotationLowerer<'a>, SpecElaborationContext) {
    let lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: StructuralClauses::empty(),
        spec_definitions,
        entry_state,
        result_type: result
            .map(ProgramValue::program_type)
            .unwrap_or(ProgramType::Int32),
        entry_values,
        aggregate_parameters: BTreeSet::new(),
        program_parameter_types: BTreeMap::new(),
        local_type_state: None,
        pointer_element_types: array_element_types,
        parameter_pointer_element_widths,
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 2_000_000,
        branch_join_target: None,
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        retained_states: Some(retained_states),
        loop_records: None,
    };
    // The proof's current locals are fixed values in every context: a name a
    // state or the entry does not bind keeps its current value, as the
    // proof reads it.
    let mut context = SpecElaborationContext {
        values: current_values
            .into_iter()
            .map(|(name, value)| (name, SpecExpression::Value(value)))
            .collect(),
        // A bound array name reads in the memory its binding names. Without
        // this an argument that names another state (`old(a)`, `at(mark, a)`)
        // would index the application's current memory instead.
        array_points: bound_array_memories.into_iter().collect(),
        ..SpecElaborationContext::default()
    };
    context.contract_result = result
        .cloned()
        .map(|value| std::sync::Arc::new(SpecExpression::Value(value)));
    context.contract_result_in_scope = context.contract_result.is_some();
    (lowerer, context)
}

/// Elaborates a fixed-state proposition with already-elaborated symbolic
/// algebraic and Integer bindings. The bindings are logical values captured at the
/// application site, so entering `old(...)` or another state keeps the
/// same value instead of re-evaluating its source expression there.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
    proposition: &ClickProposition,
    array_element_types: BTreeMap<String, ProgramType>,
    bound_array_memories: BTreeMap<String, SpecPoint>,
    entry_state: &ExecutionState,
    current_type_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
) -> Result<SpecProposition, String> {
    let (mut lowerer, context) = fixed_state_elaboration(
        array_element_types,
        bound_array_memories,
        entry_state,
        entry_values,
        current_values,
        result,
        retained_states,
        spec_definitions,
        opaque_click_functions,
        pointer_element_widths,
    );
    // A declared object has a type before it has a value. In particular,
    // forming and casting its address must not read uninitialized storage.
    lowerer.local_type_state = Some(current_type_state);
    let mut context = context;
    context.algebraic_values = algebraic_values.into_iter().collect();
    context.integer_values = integer_values.clone();
    // Reserve captured values referenced by this proposition, including native
    // machine values supplied as predicate arguments. This one source walk
    // keeps nested binders from rescanning the context.
    let mut captures = BTreeSet::<QuantifierCapture>::new();
    collect_click_proposition_referenced_bindings(proposition, &mut captures);
    let mut referenced = BTreeSet::new();
    for capture in captures {
        match capture {
            QuantifierCapture::Name(name) => {
                referenced.insert(name);
            }
            QuantifierCapture::Variable(variable) => {
                lowerer.next_quantifier_variable = lowerer.next_quantifier_variable.max(
                    variable
                        .0
                        .checked_add(1)
                        .ok_or("quantifier variable identity exhausted")?,
                );
            }
        }
    }
    lowerer.capture_referenced_names = Some(referenced.clone());
    for name in referenced {
        if let Some(value) = context.values.get(&name) {
            let captured =
                crate::kernel::SpecIntegerExpression::FromMachine(Box::new(value.clone()));
            if let Some(variable) = max_spec_integer_expression_variable(&captured) {
                lowerer.next_quantifier_variable = lowerer.next_quantifier_variable.max(
                    variable
                        .0
                        .checked_add(1)
                        .ok_or("quantifier variable identity exhausted")?,
                );
            }
        }
        if let Some(crate::kernel::SpecIntegerExpression::Term(term)) = integer_values.get(&name)
            && let Some(variable) = max_spec_integer_expression_variable(
                &crate::kernel::SpecIntegerExpression::Term(term.clone()),
            )
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
    array_element_types: BTreeMap<String, ProgramType>,
    entry_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
) -> Result<SpecAlgebraicExpression, String> {
    let (mut lowerer, mut context) = fixed_state_elaboration(
        array_element_types,
        BTreeMap::new(),
        entry_state,
        entry_values,
        current_values,
        result,
        retained_states,
        spec_definitions,
        opaque_click_functions,
        pointer_element_widths,
    );
    context.algebraic_values = algebraic_values.into_iter().collect();
    lowerer.capture_referenced_names = Some(contract_expression_referenced_names(expression));
    lowerer.lower_contract_algebraic_to_spec(expression, &context)
}

/// Elaborates an Integer expression at a fixed proof state without
/// evaluating or expanding it. This is the symbolic value captured for an
/// Integer theorem argument.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_integer_expression(
    expression: &ContractExpression,
    array_element_types: BTreeMap<String, ProgramType>,
    entry_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
) -> Result<crate::kernel::SpecIntegerExpression, String> {
    elaborate_fixed_state_integer_expression_with_integer_values(
        expression,
        array_element_types,
        entry_state,
        entry_values,
        current_values,
        &PersistentBinderMap::default(),
        BTreeMap::new(),
        result,
        retained_states,
        spec_definitions,
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
    array_element_types: BTreeMap<String, ProgramType>,
    entry_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
) -> Result<crate::kernel::SpecIntegerExpression, String> {
    let (mut lowerer, context) = fixed_state_elaboration(
        array_element_types,
        BTreeMap::new(),
        entry_state,
        entry_values,
        current_values,
        result,
        retained_states,
        spec_definitions,
        opaque_click_functions,
        pointer_element_widths,
    );
    let mut context = context;
    let mut referenced_names = BinderSet::new();
    crate::surface::lowering::collect_contract_expression_referenced_binders(
        expression,
        &mut referenced_names,
    );
    let mut referenced_integer_values = PersistentBinderMap::default();
    for name in referenced_names {
        if let Some(value) = integer_values.get(&name) {
            referenced_integer_values =
                referenced_integer_values.with_inserted(name, value.clone());
        }
    }
    context.integer_values = referenced_integer_values.clone();
    context.algebraic_values = algebraic_values.into_iter().collect();
    lowerer.capture_referenced_names = Some(contract_expression_referenced_names(expression));

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

// The same lexical walk selects named bindings and captures already embedded
// by `intro`/proof-local substitution. Neither route inspects ambient facts or
// memory: only the values in the selected proposition reserve binder identities.
#[derive(Eq, PartialEq, Ord, PartialOrd)]
enum QuantifierCapture {
    Name(String),
    Variable(Variable),
}

impl From<String> for QuantifierCapture {
    fn from(name: String) -> Self {
        Self::Name(name)
    }
}

impl ReferencedBinding for QuantifierCapture {
    fn program(binding: &crate::kernel::BindingName) -> Option<Self> {
        crate::instrumentation::record_deterministic_work(1);
        binding
            .unresolved_name()
            .map(|name| Self::Name(name.to_owned()))
    }

    fn captured_value(value: &ProgramValue, names: &mut BTreeSet<Self>) {
        crate::instrumentation::record_deterministic_work(1);
        let captured = crate::kernel::SpecIntegerExpression::FromMachine(Box::new(
            SpecExpression::Value(value.clone()),
        ));
        if let Some(variable) = max_spec_integer_expression_variable(&captured) {
            names.insert(Self::Variable(variable));
        }
    }
}

/// Finds the largest identity in the surface quantifier band nested in a
/// captured Integer binding. Fold and other high identities are already
/// disjoint; they must not push the quantifier counter into another band.
/// The kernel visitor includes both free and bound identities, including
/// those nested in machine/C payloads.
fn max_spec_integer_expression_variable(
    expression: &crate::kernel::SpecIntegerExpression,
) -> Option<crate::kernel::Variable> {
    let mut variables = BTreeSet::new();
    crate::kernel::collect_spec_integer_bound_variables(expression, &mut variables);
    variables
        .into_iter()
        .rev()
        .find(|variable| variable.0 < SURFACE_QUANTIFIER_VARIABLE_CEILING)
}

/// Elaborates an expression stated in a fixed-state proof into the kernel's
/// spec form, as `elaborate_fixed_state_proposition` does a proposition; the
/// kernel then evaluates the result at the proof's state.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_expression(
    expression: &ContractExpression,
    array_element_types: BTreeMap<String, ProgramType>,
    entry_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
) -> Result<SpecExpression, String> {
    elaborate_fixed_state_expression_with_algebraic_values(
        expression,
        array_element_types,
        entry_state,
        entry_values,
        current_values,
        BTreeMap::new(),
        result,
        retained_states,
        spec_definitions,
        opaque_click_functions,
        pointer_element_widths,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_expression_with_algebraic_values(
    expression: &ContractExpression,
    array_element_types: BTreeMap<String, ProgramType>,
    entry_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
) -> Result<SpecExpression, String> {
    elaborate_fixed_state_expression_with_algebraic_and_integer_values(
        expression,
        array_element_types,
        entry_state,
        entry_values,
        current_values,
        algebraic_values,
        &PersistentBinderMap::default(),
        result,
        retained_states,
        spec_definitions,
        opaque_click_functions,
        pointer_element_widths,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn elaborate_fixed_state_expression_with_algebraic_and_integer_values(
    expression: &ContractExpression,
    array_element_types: BTreeMap<String, ProgramType>,
    entry_state: &ExecutionState,
    entry_values: ProgramValueBindings,
    current_values: ProgramValueBindings,
    algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    result: Option<&ProgramValue>,
    retained_states: &RecordedStates,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: BTreeSet<String>,
    pointer_element_widths: BTreeMap<String, u32>,
) -> Result<SpecExpression, String> {
    let (mut lowerer, mut context) = fixed_state_elaboration(
        array_element_types,
        BTreeMap::new(),
        entry_state,
        entry_values,
        current_values,
        result,
        retained_states,
        spec_definitions,
        opaque_click_functions,
        pointer_element_widths,
    );
    context.algebraic_values = algebraic_values.into_iter().collect();
    // Capture only bindings mentioned by this argument. Reserve their Integer
    // identities before a nested fold or function allocates fresh binders.
    let names = contract_expression_referenced_names(expression);

    for name in &names {
        if let Some(value) = integer_values.get(name) {
            context.integer_values = context
                .integer_values
                .with_inserted(name.clone(), value.clone());
            if let Some(variable) = max_spec_integer_expression_variable(value) {
                lowerer.next_quantifier_variable = lowerer.next_quantifier_variable.max(
                    variable
                        .0
                        .checked_add(1)
                        .ok_or("quantifier variable identity exhausted")?,
                );
            }
        }
    }
    // A state the expression enters reads only these names, as for a
    // proposition, rather than every local the state's state binds.
    lowerer.capture_referenced_names = Some(names);
    lowerer.lower_contract_expression_to_spec(expression, &context)
}

/// Elaborates one `requires` proposition into the kernel's spec form, exactly
/// as `function_contract_summary` elaborates the contract's clauses; the
/// kernel then lowers it at the function's entry state. A predicate call
/// stays a predicate.
///
/// `entry_state` is the state the kernel lowers the result at. Its bindings
/// give a file-scope array its declared element type, as the contract
/// summary's entry state does: elaborated over an empty state, `bytes[6]` of
/// a `uint8 bytes[8]` defaulted to an `int32` load at byte 24, a different
/// cell from the one the C program and every other clause read.
pub(in crate::surface) fn elaborate_requirement_proposition(
    parameter_binding: ParameterBinding<'_>,
    entry_state: &ExecutionState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<SpecProposition, String> {
    // A requirement reads only the parameters it names: with the binding's
    // index, the parameter tables hold those alone.
    let parameters: Vec<&crate::languages::interface::ImportedParameter> =
        match parameter_binding.index {
            Some(index) => {
                let mut names = BTreeSet::new();
                crate::surface::lowering::collect_click_proposition_referenced_names(
                    proposition,
                    &mut names,
                );
                names
                    .iter()
                    .filter_map(|name| index.position(name))
                    .map(|position| &parameter_binding.parameters[position])
                    .collect()
            }
            None => parameter_binding.parameters.iter().collect(),
        };
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: StructuralClauses::empty(),
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        spec_definitions,
        entry_state,
        result_type: ProgramType::Int32,
        entry_values: ProgramValueBindings::new(),
        aggregate_parameters: BTreeSet::new(),
        program_parameter_types: parameters
            .iter()
            .map(|parameter| {
                (
                    parameter.name().to_string(),
                    parameter.interface_type().to_kernel_type(),
                )
            })
            .collect(),
        local_type_state: None,
        pointer_element_types: parameters
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parameters.iter().copied(),
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
        branch_join_target: None,
        retained_states: None,
        loop_records: None,
    };
    lowerer.click_proposition_to_spec_proposition(
        proposition,
        &SpecElaborationContext::for_function_contract(),
    )
}

/// The block with each frontier loop clause resolved through the proof scope
/// it was written under, so a clause written inside a proof `match` arm lowers
/// with that arm's bindings exactly as a `have` there would.
fn resolved_function_block(
    function_block: &FunctionBlock,
) -> Result<std::borrow::Cow<'_, FunctionBlock>, ClickError> {
    function_block
        .with_resolved_structural_clauses()
        .map_err(|message| {
            ClickError::new(format!("could not resolve loop clause bindings: {message}"))
        })
}

pub(in crate::surface) fn function_contract_summary(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    spec_definitions: SpecDefinitions<'_>,
    _resource_environment: &ResourceEnvironment,
) -> Result<FunctionContractSummary, ClickError> {
    let resolved_block = resolved_function_block(function_block)?;
    let function_block: &FunctionBlock = &resolved_block;
    let entry_state = crate::kernel::initialize_program_function_globals(
        &ExecutionState::new().with_population_creation_tracking(),
        &parsed_function.to_kernel_function(),
    );
    let mut lowerer = AnnotationLowerer {
        capture_referenced_names: None,
        source_bindings: None,
        structural_clauses: function_block.structural_clauses(),
        implicit_contract_mutable_segments: &[],
        loop_resources: BTreeMap::new(),
        inherits_resource_derived_frame: false,
        spec_definitions,
        entry_state: &entry_state,
        result_type: parsed_function.return_type().to_kernel_type(),
        entry_values: ProgramValueBindings::new(),
        aggregate_parameters: BTreeSet::new(),
        program_parameter_types: parsed_function
            .parameters()
            .iter()
            .map(|parameter| {
                (
                    parameter.name().to_string(),
                    parameter.interface_type().to_kernel_type(),
                )
            })
            .collect(),
        local_type_state: None,
        pointer_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.interface_type())?,
                ))
            })
            .collect(),
        parameter_pointer_element_widths: parameter_pointer_element_widths(
            parsed_function.parameters(),
        ),
        quantified_values: BinderMap::new(),
        algebraic_variables: BinderMap::new(),
        algebraic_types: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
        branch_join_target: None,
        retained_states: None,
        loop_records: None,
    };
    let mut context = SpecElaborationContext::for_function_contract();
    // Parameters shadow file-scope spellings in both current and old clauses.
    // Keep them as C bindings, not loads from same-named global storage.
    context.values.extend(
        parsed_function
            .parameters()
            .iter()
            .filter(|parameter| !parameter.is_reference())
            .map(|parameter| {
                // Reference expressions already retain their typed carrier. They
                // are program bindings, never lexical aliases of pointer values.
                let name = parameter.name().to_owned();
                (
                    name,
                    SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        parameter.binding_name().clone(),
                    )),
                )
            }),
    );
    let all_predicates = spec_definitions
        .predicates
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let unfold_contract_predicates = |proposition: &ClickProposition| {
        // Apply the predicate's character-byte adapter before substitution:
        // otherwise its uint8 reads inherit the caller parameter's signed
        // char type, unlike the predicate used by the entry proof.
        let elaborated =
            elaborate_character_byte_views(proposition, spec_definitions.predicates, &|name| {
                parsed_function
                    .parameters()
                    .iter()
                    .find(|parameter| parameter.name() == name)
                    .map(crate::languages::interface::ImportedParameter::interface_type)
            });
        unfold_click_predicates_in_proposition_with_active(
            spec_definitions.predicates,
            &all_predicates,
            elaborated.as_ref().unwrap_or(proposition),
            &mut BTreeSet::new(),
        )
    };
    let mut opaque_contract_supported = true;
    clear_opaque_contract_refusal(function_block.signature().name());
    let mut predicate_unfoldings = Vec::new();
    let mut requires = Vec::new();
    let mut contract_requirement_sources = Vec::new();
    for proposition in requirement_definedness_surfaces(function_block.requires()) {
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => {
                requires.push(proposition);
                contract_requirement_sources.push(None);
            }
            Err(error) => {
                opaque_contract_supported = false;
                note_opaque_contract_refusal(function_block.signature().name(), &error);
            }
        }
    }
    for (source_index, requirement) in function_block.requires().iter().enumerate() {
        let proposition = match requirement {
            Requirement::Proposition(proposition) => proposition.clone(),
            Requirement::LoadableSegment { segment } => ClickProposition::Loadable {
                segment: segment.clone(),
            },
            Requirement::Resource(_) => continue,
        };
        let mut called = BTreeSet::new();
        crate::surface::validation::collect_called_predicates(&proposition, &mut called);
        let opaque_predicate = called
            .iter()
            .any(|name| spec_definitions.predicates.get(name).is_some())
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
                    predicate_unfoldings.push(
                        PredicateUnfolding::new(predicate, proposition.clone())
                            .with_requirement_source(source_index),
                    );
                }
                requires.push(proposition);
                contract_requirement_sources.push(Some(source_index));
            }
            Err(error) => {
                opaque_contract_supported = false;
                note_opaque_contract_refusal(function_block.signature().name(), &error);
            }
        }
    }
    // Entry reads use the live argument image. Exit clauses project logical
    // values independently of the parameter's expired C storage.
    lowerer.aggregate_parameters = parsed_function
        .parameters()
        .iter()
        .filter(|parameter| parameter.is_struct_value())
        .map(|parameter| parameter.name().to_string())
        .collect();
    let mut ensures = Vec::new();
    // A postcondition is read in the exit state, where `result` is the
    // contract result.
    let mut ensures_context = context.clone();
    ensures_context.contract_result_in_scope = true;
    for proposition in function_block
        .ensures()
        .iter()
        .filter_map(|clause| match clause.ensure() {
            Ensure::Proposition(proposition) => Some(proposition),
            Ensure::Resource(_) => None,
        })
    {
        let mut called = BTreeSet::new();
        crate::surface::validation::collect_called_predicates(proposition, &mut called);
        let opaque_predicate = called
            .iter()
            .any(|name| spec_definitions.predicates.get(name).is_some())
            .then(|| lowerer.click_proposition_to_spec_proposition(proposition, &ensures_context))
            .transpose();
        let Ok(proposition) = unfold_contract_predicates(proposition) else {
            opaque_contract_supported = false;
            continue;
        };
        if !proposition_supported_in_opaque_contract(&proposition) {
            opaque_contract_supported = false;
            continue;
        }
        match lowerer.click_proposition_to_spec_proposition(&proposition, &ensures_context) {
            Ok(proposition) => {
                if let Ok(Some(predicate)) = opaque_predicate {
                    predicate_unfoldings
                        .push(PredicateUnfolding::new(predicate, proposition.clone()));
                }
                ensures.push(proposition)
            }
            Err(error) => {
                opaque_contract_supported = false;
                note_opaque_contract_refusal(function_block.signature().name(), &error);
            }
        }
    }

    let mut exceptional_ensures = Vec::new();
    let mut exceptional_context = context.clone();
    exceptional_context.contract_result = None;
    exceptional_context.values.insert(
        "exception".to_string(),
        SpecExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::CONTRACT_EXCEPTION,
        )),
    );
    for clause in function_block.exceptional_ensures() {
        let Ensure::Proposition(proposition) = clause.ensure() else {
            opaque_contract_supported = false;
            continue;
        };
        if !proposition_supported_in_opaque_contract(proposition) {
            opaque_contract_supported = false;
            continue;
        }
        match lowerer.click_proposition_to_spec_proposition(proposition, &exceptional_context) {
            Ok(proposition) => exceptional_ensures.push(proposition),
            Err(error) => {
                opaque_contract_supported = false;
                note_opaque_contract_refusal(function_block.signature().name(), &error);
            }
        }
    }

    let mut mutable = Vec::new();
    {
        if let Some(startup) = &parsed_function.program_entry_state {
            mutable.extend(startup.resources().facts().iter().filter_map(|fact| {
                // Program-entry resources are concrete C globals, built with
                // signed int32 bounds by the program-entry initializer.
                let range = fact.memory_own_range()?;
                Some(
                    MemorySegment::new(
                        ProgramExpression::Value(ProgramValue::pointer(range.base().clone())),
                        ProgramExpression::Value(ProgramValue::Int32(range.start().clone())),
                        ProgramExpression::Value(ProgramValue::Int32(range.end().clone())),
                    )
                    .with_element_width(range.element_width()),
                )
            }));
        }
    }
    let mut claims = if function_block.ensures().is_empty()
        && function_block.exceptional_ensures().is_empty()
    {
        vec![FunctionContractClaim::body_safety()]
    } else {
        let mut proposition_index = 0;
        let mut resource_index = 0;
        let mut claims = Vec::new();
        for (source_index, ensure) in function_block.ensures().iter().enumerate() {
            claims.push(match ensure.ensure() {
                Ensure::Proposition(_) => {
                    let claim =
                        FunctionContractClaim::ensure_proposition(source_index, proposition_index);
                    proposition_index += 1;
                    claim
                }
                Ensure::Resource(_) => {
                    let claim =
                        FunctionContractClaim::ensure_resource(source_index, resource_index);
                    resource_index += 1;
                    claim
                }
            });
        }
        for (source_index, _ensure) in function_block.exceptional_ensures().iter().enumerate() {
            claims.push(FunctionContractClaim::exceptional_ensure_proposition(
                source_index,
                source_index,
            ));
        }
        claims
    };
    // The hidden destination owner is returned just like an explicit owned
    // resource. Certify that transition from the body, even though its clause
    // is supplied by the frontend rather than written in the sidecar.
    if super::resource_lowering::construction_result_layout(parsed_function).is_some() {
        let resource_index = function_block
            .ensures()
            .iter()
            .filter(|clause| matches!(clause.ensure(), Ensure::Resource(_)))
            .count();
        claims.push(FunctionContractClaim::ensure_resource(
            function_block.ensures().len(),
            resource_index,
        ));
    }
    let recursion_measure = lowerer.function_recursion_measure(function_block, &context)?;
    Ok((
        requires,
        contract_requirement_sources,
        ensures,
        exceptional_ensures,
        mutable,
        claims,
        opaque_contract_supported,
        predicate_unfoldings,
        recursion_measure,
    ))
}

fn proposition_supported_in_opaque_contract(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Value(_) => true,
        ClickProposition::Separate { .. }
        | ClickProposition::ResourceViewable { .. }
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

/// The pointee type of each of `parsed_function`'s local pointers and arrays,
/// for a caller that annotates the function repeatedly and indexes it once
/// (`SourceExecutionLayout::local_pointer_element_types`).
pub(in crate::surface) fn local_pointer_element_types(
    parsed_function: &crate::languages::interface::ImportedFunction,
) -> BTreeMap<String, ProgramType> {
    let mut types = BTreeMap::new();
    collect_local_pointer_element_types(parsed_function.to_kernel_function().body(), &mut types);
    types
}

/// Index declarations once, before any loop resource or invariant is lowered.
/// Frontends give shadowed locals distinct kernel names; this index records
/// types, never values or read authority, and never walks execution history.
fn collect_local_pointer_element_types(
    body: &ProgramStatement,
    types: &mut BTreeMap<String, ProgramType>,
) {
    let mut pending = vec![body];
    while let Some(statement) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match statement {
            ProgramStatement::Declare {
                name, program_type, ..
            } => {
                let element = program_type.pointee_type().or(match program_type {
                    ProgramType::Int8Array(_) => Some(ProgramType::Int8),
                    ProgramType::Int16Array(_) => Some(ProgramType::Int16),
                    ProgramType::Int32Array(_) => Some(ProgramType::Int32),
                    ProgramType::Int64Array(_) => Some(ProgramType::Int64),
                    ProgramType::Int128Array(_) => Some(ProgramType::Int128),
                    ProgramType::UInt8Array(_) => Some(ProgramType::UInt8),
                    ProgramType::UInt16Array(_) => Some(ProgramType::UInt16),
                    ProgramType::UInt32Array(_) => Some(ProgramType::UInt32),
                    ProgramType::UInt64Array(_) => Some(ProgramType::UInt64),
                    ProgramType::UInt128Array(_) => Some(ProgramType::UInt128),
                    ProgramType::Float32Array(_) => Some(ProgramType::Float32),
                    ProgramType::Float64Array(_) => Some(ProgramType::Float64),
                    _ => None,
                });
                if let Some(element) = element
                    && let Some(name) = name.named()
                {
                    types.insert(name.to_owned(), element);
                }
            }
            ProgramStatement::Seq(statements) => {
                // The pair nodes beyond the first the tree held.
                crate::instrumentation::record_deterministic_work(statements.len() - 2);
                pending.extend(statements.iter().map(|statement| statement.as_ref()))
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => pending.extend([then_branch.as_ref(), else_branch.as_ref()]),
            ProgramStatement::Loop {
                test: loop_test,
                update,
                body,
                ..
            } => {
                let test = loop_test.source_region();
                pending.push(body);
                if let Some(test) = test {
                    pending.push(&test.statement);
                }
                if let Some(update) = update {
                    pending.push(update);
                }
            }

            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            }
            | ProgramStatement::UnwindCleanup {
                body: try_body,
                cleanup: handler,
            } => pending.extend([try_body.as_ref(), handler.as_ref()]),
            ProgramStatement::Switch { cases, .. } => {
                pending.extend(cases.iter().map(|case| case.body.as_ref()))
            }
            _ => {}
        }
    }
}

/// Lowers each loop's `owns` and `views` clauses once for the function.
///
/// A loop declaration is the same contract shape as a callee's: the owned
/// memory is the loop's checked write footprint, and the declarations together
/// are the resource context its body executes with.
fn loop_resource_declarations(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    resource_environment: &ResourceEnvironment,
    lowerer: &mut AnnotationLowerer<'_>,
) -> Result<BTreeMap<usize, LoopResourceDeclaration>, ClickError> {
    let mut declarations: BTreeMap<usize, LoopResourceDeclaration> = BTreeMap::new();
    let mut source_layout = None;
    for clause in function_block.structural_clauses() {
        let CodeRegion::Loop(loop_index) = clause.region() else {
            continue;
        };
        if clause.resources().is_empty() {
            continue;
        }
        if source_layout.is_none() && parsed_function.prelowered_kernel_function().is_none() {
            source_layout = Some(SourceExecutionLayout::for_function(parsed_function)?);
        }
        let bindings = source_layout.as_ref().and_then(|layout| {
            let head = layout
                .execution_region_entry(CodeRegion::Loop(*loop_index))
                .ok()?;
            layout.site(head)?.source_bindings()
        });
        let mut names = BTreeSet::new();
        for resource in clause.resources() {
            collect_current_resource_clause_variables(resource, &mut names);
        }
        let pointer_types = names
            .into_iter()
            .filter_map(|name| {
                let element = bindings
                    .and_then(|bindings| bindings.get(&name))
                    .and_then(|(_, binding)| binding.program_type())
                    .and_then(|ty| ty.pointee_type().or_else(|| ty.array_element_type()))
                    .or_else(|| lowerer.pointer_element_types.get(&name).copied())?;
                Some((name, element))
            })
            .collect();
        let declaration = declarations.entry(*loop_index).or_default();
        for resource in clause.resources() {
            if let ResourceClause::Conditional {
                condition,
                resource,
            } = resource
            {
                let guard = lowerer
                    .click_proposition_to_spec_proposition(
                        condition,
                        &SpecElaborationContext::for_loop_invariant(*loop_index),
                    )
                    .map_err(ClickError::new)?;
                let start = declaration.specs.len();
                append_entry_resource_specs_with_pointer_types(
                    resource,
                    parsed_function.parameters(),
                    &pointer_types,
                    &mut declaration.specs,
                )?;
                for spec in &mut declaration.specs[start..] {
                    *spec = spec.clone().with_guard(guard.clone());
                }
                continue;
            }
            let resource = &loop_resource_with_field_schema(resource, resource_environment)?;
            append_entry_resource_specs_with_pointer_types(
                resource,
                parsed_function.parameters(),
                &pointer_types,
                &mut declaration.specs,
            )?;
        }
    }
    for declaration in declarations.values_mut() {
        for spec in &mut declaration.specs {
            *spec = spec
                .clone()
                .with_captured_entry_parameters(&lowerer.entry_values);
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
pub(in crate::surface) fn loop_resource_with_field_schema(
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

/// A loop's declared resources, lowered once for the enclosing function.
#[derive(Clone, Debug, Default)]
struct LoopResourceDeclaration {
    /// The loop's declarations as kernel resource specs, evaluated at loop
    /// entry to build the body's resource context and, from that same
    /// evaluation, the loop's checked whole-loop footprint.
    specs: Vec<ResourceSpec>,
}

struct AnnotationLowerer<'a> {
    capture_referenced_names: Option<BTreeSet<String>>,
    source_bindings: Option<syntax::CSourceBindings>,
    structural_clauses: &'a StructuralClauses,
    implicit_contract_mutable_segments: &'a [MemorySegment],
    /// Resources declared by each loop, keyed by loop index. A loop with a
    /// declaration has the shape of a callee contract: its body executes
    /// owning exactly these resources, and its write footprint is the memory
    /// they own rather than everything the function owns.
    loop_resources: BTreeMap<usize, LoopResourceDeclaration>,
    /// Whether this function's write footprint comes from its resources. A
    /// loop in such a function inherits that footprint, so an empty one is an
    /// inherited empty footprint rather than the absence of one.
    inherits_resource_derived_frame: bool,
    spec_definitions: SpecDefinitions<'a>,
    entry_state: &'a ExecutionState,
    result_type: ProgramType,
    entry_values: ProgramValueBindings,
    /// Live declaration types for state-parametric branch facts; values remain symbolic.
    /// Each referenced name uses the state's existing index, without a body/history scan.
    local_type_state: Option<&'a ExecutionState>,
    /// Declared C types of the function's parameters, where a function is
    /// in scope: a clause's range over a `size_t` parameter is a `size_t`
    /// range.
    program_parameter_types: BTreeMap<String, ProgramType>,
    /// Declared pointee types of parameters and encountered automatic locals.
    /// Local names are the frontend's distinct kernel bindings.
    pointer_element_types: BTreeMap<String, ProgramType>,
    aggregate_parameters: BTreeSet<String>,
    /// Source-side pointee widths which are not representable in the kernel's
    /// nominal `ProgramType` (notably pointers to structs, which use the compatible
    /// `int32*` carrier).  Pointer arithmetic must retain this physical width.
    parameter_pointer_element_widths: BTreeMap<String, u32>,
    quantified_values: BinderMap<ProgramValue>,
    algebraic_variables: BinderMap<SpecAlgebraicExpression>,
    algebraic_types: BTreeMap<(String, Vec<AlgebraicValueType>), AlgebraicType>,
    loop_index: usize,
    statement_index: usize,
    next_quantifier_variable: u64,
    branch_join_target: Option<&'a ProgramPointRef>,
    /// The states a proof recorded at program points and marks, when the
    /// proposition is stated inside a proof.
    retained_states: Option<&'a RecordedStates>,
    /// What a whole-function walk saw at each loop it lowered, in loop
    /// order, when a later annotation may lower one loop alone
    /// (`LoopAnnotation`).
    loop_records: Option<Vec<LoopLoweringRecord>>,
}

/// Debug builds only: `CLICK_DEBUG_CHECK_LOOP_ANNOTATIONS=1` checks every
/// `loop` tactic's annotation against a whole-function walk, for corpus
/// validation.
#[cfg(debug_assertions)]
pub(in crate::surface) fn loop_annotation_check_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var_os("CLICK_DEBUG_CHECK_LOOP_ANNOTATIONS").is_some_and(|value| value == "1")
    })
}

#[cfg(test)]
thread_local! {
    static ANNOTATION_WALKS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Counts, in test builds, whole-function annotation walks made for `loop`
/// tactics.
fn count_annotation_walks(_walks: usize) {
    #[cfg(test)]
    ANNOTATION_WALKS.with(|count| count.set(count.get() + _walks));
}

/// The whole-function annotation walks `loop` tactics made on this thread.
#[cfg(test)]
pub(in crate::surface) fn loop_annotation_walks() -> usize {
    ANNOTATION_WALKS.with(std::cell::Cell::get)
}

/// What the lowering walk saw at one loop.
#[derive(Clone, Copy, Debug)]
struct LoopLoweringRecord {
    /// The statement counter at the loop's own node.
    statement_index: usize,
    /// Whether the loop is a `while` or `do` loop whose body holds no loop,
    /// so lowering its node alone lowers exactly that loop.
    lowered_alone: bool,
    /// The quantifier counter once the loop was lowered.
    quantifiers_after: u64,
    /// Whether the walk's scoped bindings were empty once the loop was
    /// lowered, so the next loop starts from none.
    bindings_empty_after: bool,
}

/// [`parameter_pointer_element_widths`] for the parameters among `names`,
/// found through the binding's index when it has one.
pub(in crate::surface) fn parameter_pointer_element_widths_named(
    parameter_binding: ParameterBinding<'_>,
    names: &BTreeSet<String>,
) -> BTreeMap<String, u32> {
    let Some(index) = parameter_binding.index else {
        return parameter_pointer_element_widths(parameter_binding.parameters);
    };
    parameter_pointer_element_widths(
        names
            .iter()
            .filter_map(|name| Some(&parameter_binding.parameters[index.position(name)?])),
    )
}

pub(in crate::surface) fn parameter_pointer_element_widths<'a>(
    parameters: impl IntoIterator<Item = &'a crate::languages::interface::ImportedParameter>,
) -> BTreeMap<String, u32> {
    parameters
        .into_iter()
        .filter_map(|parameter| {
            parameter
                .array_element_width()
                .or_else(|| {
                    parameter
                        .interface_type()
                        .pointee_type()
                        .filter(|ty| ty.is_pointer())
                        .map(|ty| ty.to_kernel_type().byte_width())
                })
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
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> BTreeMap<String, u32> {
    parameters
        .iter()
        .filter_map(|parameter| {
            parameter
                .click_type()
                .interface_type()
                .and_then(|ty| ty.pointee_type())
                .filter(|ty| ty.is_pointer())
                .map(|ty| {
                    (
                        parameter.name().to_string(),
                        ty.to_kernel_type().byte_width(),
                    )
                })
                .or_else(|| {
                    parameter
                        .struct_name()
                        .and_then(|name| struct_layouts.get(name))
                        .map(|layout| (parameter.name().to_string(), layout.size_bytes()))
                })
                .or_else(|| {
                    parameter
                        .click_type()
                        .interface_type()
                        .and_then(click_array_element_type)
                        .map(|element| (parameter.name().to_string(), element.byte_width()))
                })
        })
        .collect()
}

/// Lower explicit arithmetic evidence without constructing or cloning a C
/// state. Its only environment is the already captured mathematical bindings.
pub(in crate::surface) fn lower_integer_arithmetic_proposition(
    proposition: &ClickProposition,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
) -> Result<Proposition, String> {
    check_integer_lowering_work(1)?;
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let root = lower_surface_integer_comparison(left, *operator, right, integer_values)?;
            // Propositions still store native condition descriptors. This is the
            // explicit output boundary, after both operands have stayed shared.
            let condition = crate::kernel::KernelTermExport::condition(&root)?;
            Ok(Proposition::condition_is(condition, true))
        }
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_integer_arithmetic_proposition(body, integer_values)?,
        ))),
        _ => Err("an Integer certificate requires a mathematical comparison".into()),
    }
}

/// The decimal spelling of an integer literal, negated or not.
fn integer_literal_spelling(expression: &ContractExpression) -> Option<String> {
    match expression {
        ContractExpression::IntegerLiteral(text) => Some(text.clone()),
        ContractExpression::Negate(inner) => match inner.as_ref() {
            ContractExpression::IntegerLiteral(text) => Some(format!("-{text}")),
            _ => None,
        },
        _ => None,
    }
}

/// The value of an integer constant built only from unsuffixed literals and
/// `+`, `-`, `*`, as a decimal spelling: `3 - 1` is `2`. Such a constant has
/// no type of its own, so a typed position takes it as a literal of that
/// type. `None` for anything else, or past `i128`.
fn integer_constant_spelling(expression: &ContractExpression) -> Option<String> {
    fn value(expression: &ContractExpression) -> Option<i128> {
        match expression {
            ContractExpression::IntegerLiteral(text) => text.parse().ok(),
            ContractExpression::Negate(inner) => value(inner)?.checked_neg(),
            ContractExpression::Add(left, right) => value(left)?.checked_add(value(right)?),
            ContractExpression::Subtract(left, right) => value(left)?.checked_sub(value(right)?),
            ContractExpression::Multiply(left, right) => value(left)?.checked_mul(value(right)?),
            _ => None,
        }
    }
    value(expression).map(|value| value.to_string())
}

/// Explicit compatibility result for remaining theorem and deferred-expression
/// consumers. Certificate comparisons use the common-root entry point below.
pub(in crate::surface) fn lower_contract_integer_to_spec(
    expression: &SurfaceTerm,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
) -> Result<crate::kernel::SpecIntegerExpression, String> {
    let term = lower_surface_integer_term(expression, integer_values)?;
    let value = crate::kernel::KernelTermExport::default().integer(&term)?;
    Ok(crate::kernel::SpecIntegerExpression::Term(
        value.as_ref().clone(),
    ))
}

/// Lower one mathematical comparison directly from its typed common operands.
pub(in crate::surface) fn lower_surface_integer_comparison(
    left: &SurfaceTerm,
    operator: ComparisonOperator,
    right: &SurfaceTerm,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
) -> Result<crate::kernel::KernelTerm, String> {
    let left = lower_surface_integer_term(left, integer_values)?;
    let right = lower_surface_integer_term(right, integer_values)?;
    check_integer_lowering_work(
        integer_kernel_root_work(&left).saturating_add(integer_kernel_root_work(&right)),
    )?;
    crate::kernel::KernelTerm::integer_comparison(
        integer_comparison_operator(operator)?,
        [left, right],
    )
    .map_err(str::to_owned)
}

fn integer_kernel_root_work(term: &crate::kernel::KernelTerm) -> usize {
    match term.node() {
        crate::kernel::KernelTermNode::IntegerLiteral(value) => value.bits() as usize + 1,
        _ => 1,
    }
}

/// Arithmetic step operands remain typed common roots.
/// Bindings are looked up by name; neither facts nor unrelated bindings are
/// traversed. Native condition storage is an explicit final output adapter.
pub(in crate::surface) fn lower_surface_integer_term(
    expression: &SurfaceTerm,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
) -> Result<crate::kernel::KernelTerm, String> {
    fn lower(
        expression: &SurfaceTerm,
        integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
        locals: &PersistentBinderMap<crate::kernel::KernelTerm>,
        importer: &mut crate::kernel::KernelTermImport,
    ) -> Result<crate::kernel::KernelTerm, String> {
        use crate::kernel::{KernelIntegerOperator as Op, KernelTerm, SpecIntegerExpression};
        check_integer_lowering_work(1)?;
        if let Some(reduced) = lambdas::reduce_head(expression)? {
            return lower(&reduced, integer_values, locals, importer);
        }
        if let Some(id) = expression.generated_binder() {
            if let Some(value) = locals.get(&id) {
                return Ok(value.clone());
            }
            if let Some(SpecIntegerExpression::Term(term)) = integer_values.get(&id) {
                return Ok(importer.integer(&term.clone().into()));
            }
            return Err(format!("`{id}` is not an Integer binding"));
        }
        match expression {
            SurfaceTerm::IntegerContext(value) => lower(value, integer_values, locals, importer),
            SurfaceTerm::IntegerLiteral(value) => {
                check_integer_lowering_work(
                    value.len().saturating_mul(value.len().saturating_add(4)),
                )?;
                let value = value
                    .parse::<num_bigint::BigInt>()
                    .map_err(|_| format!("invalid Integer literal `{value}`"))?;
                Ok(KernelTerm::integer_literal(value))
            }
            SurfaceTerm::Binding(name) => {
                if let Some(value) = locals.get(name) {
                    check_integer_lowering_work(integer_kernel_root_work(value))?;
                    return Ok(value.clone());
                }
                let value = integer_values
                    .get(name)
                    .ok_or_else(|| format!("`{name}` is not an Integer binding"))?;
                let SpecIntegerExpression::Term(term) = value else {
                    return Err(
                        "machine-backed Integer bindings require fixed-state capture".into(),
                    );
                };
                check_integer_lowering_work(integer_root_work(term))?;
                Ok(importer.integer(&term.clone().into()))
            }
            SurfaceTerm::Negate(inner) => {
                if let Some(literal) = integer_literal_spelling(expression) {
                    return lower(
                        &SurfaceTerm::IntegerLiteral(literal),
                        integer_values,
                        locals,
                        importer,
                    );
                }
                let value = lower(inner, integer_values, locals, importer)?;
                check_integer_lowering_work(integer_kernel_root_work(&value))?;
                KernelTerm::integer_operation(Op::Negate, vec![value]).map_err(Into::into)
            }
            SurfaceTerm::Add(left, right)
            | SurfaceTerm::Subtract(left, right)
            | SurfaceTerm::Multiply(left, right) => {
                let left = lower(left, integer_values, locals, importer)?;
                let right = lower(right, integer_values, locals, importer)?;
                let operator = match expression {
                    SurfaceTerm::Add(..) => Op::Add,
                    SurfaceTerm::Subtract(..) => Op::Subtract,
                    _ => Op::Multiply,
                };
                let work = if operator == Op::Multiply {
                    integer_kernel_root_work(&left).saturating_mul(integer_kernel_root_work(&right))
                } else {
                    integer_kernel_root_work(&left).saturating_add(integer_kernel_root_work(&right))
                };
                check_integer_lowering_work(work)?;
                KernelTerm::integer_operation(operator, vec![left, right]).map_err(Into::into)
            }
            SurfaceTerm::Let {
                name,
                click_type: Some(ClickType::Integer),
                value,
                body,
            } => {
                let value = lower(value, integer_values, locals, importer)?;
                lower(
                    body,
                    integer_values,
                    &locals.with_inserted(name.clone(), value),
                    importer,
                )
            }
            _ => Err("expected a specification-side Integer expression".into()),
        }
    }
    lower(
        expression,
        integer_values,
        &Default::default(),
        &mut Default::default(),
    )
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
    use crate::kernel::{KernelIntegerOperator as Op, SpecIntegerExpression};
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
    let operator = match operation {
        IntegerOperation::Add => Op::Add,
        IntegerOperation::Subtract => Op::Subtract,
        IntegerOperation::Multiply => Op::Multiply,
    };
    construct_integer_operation(operator, vec![left, right])
}

/// Ordinary specification arithmetic shares the certificate term constructor.
/// Deferred evaluation remains in SpecIntegerExpression until its operands
/// become values; this bridge neither evaluates them nor discharges obligations.
fn construct_integer_operation(
    operator: crate::kernel::KernelIntegerOperator,
    operands: Vec<crate::kernel::IntegerTerm>,
) -> Result<crate::kernel::SpecIntegerExpression, String> {
    use crate::kernel::{KernelTerm, KernelTermExport, KernelTermImport, SpecIntegerExpression};
    let mut importer = KernelTermImport::default();
    let arguments = operands
        .into_iter()
        .map(|operand| importer.integer(&operand.into()))
        .collect();
    let term = KernelTerm::integer_operation(operator, arguments)?;
    let value = KernelTermExport::default().integer(&term)?;
    Ok(SpecIntegerExpression::Term(value.as_ref().clone()))
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
                crate::kernel::SharedPureApplication::intern(
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
    fn source_binding(&self, name: crate::kernel::BindingName) -> crate::kernel::BindingName {
        name.named()
            .and_then(|name| self.source_bindings.as_ref()?.get(name))
            .map(|(_, binding)| binding.clone())
            .unwrap_or(name)
    }

    fn declared_pointer_element_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
    ) -> Option<ProgramType> {
        let name = self.source_binding(name.into());
        if name == crate::kernel::CONTRACT_RESULT {
            return self
                .result_type
                .pointee_type()
                .or_else(|| self.result_type.array_element_type());
        }
        if name.unresolved_name().is_none() {
            return name
                .program_type()
                .and_then(|ty| ty.pointee_type().or_else(|| ty.array_element_type()));
        }
        self.local_type_state
            .and_then(|state| {
                state
                    .local_object_type(&name)
                    .and_then(|ty| ty.pointee_type())
                    // A local array, such as `char tmp[12]`, is indexed by
                    // its element type, as a fixed-state proof reads it.
                    .or_else(|| state.locals().array_object_element_type(&name))
            })
            .or_else(|| name.metadata_in(&self.pointer_element_types).copied())
    }

    /// Attach the same checked loop clauses to compiler-lowered statements.
    fn lower_kernel_statement(
        &mut self,
        statement: &ProgramStatement,
    ) -> Result<ProgramStatement, ClickError> {
        Ok(match statement {
            ProgramStatement::Seq(statements) => {
                ProgramStatement::Seq(statements.try_map(|statement| {
                    self.lower_kernel_statement(statement)
                        .map(std::sync::Arc::new)
                })?)
            }
            ProgramStatement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.next_statement_index();
                program_if(
                    condition.clone(),
                    self.lower_kernel_statement(then_branch)?,
                    self.lower_kernel_statement(else_branch)?,
                )
            }
            ProgramStatement::Loop {
                test: loop_test,
                update,
                invariant,
                invariant_checks,
                effect_checks,
                resource_specs,
                ranking_measures,
                structural_measure,
                backedge_target,
                natural_exit_target,
                body,
            } => {
                let test = loop_test.source_region();
                self.next_statement_index();
                let index = self.next_loop_index();
                let mut lowered_test = None;
                if let Some(test) = test
                    .as_ref()
                    .filter(|test| test.position == crate::kernel::LoopTestPosition::BeforeBody)
                {
                    lowered_test = Some(crate::kernel::LoopTestRegion {
                        statement: std::sync::Arc::new(
                            self.lower_kernel_statement(&test.statement)?,
                        ),
                        position: test.position,
                    });
                }
                let body = self.lower_kernel_statement(body)?;
                let update = update
                    .as_ref()
                    .map(|step| self.lower_kernel_statement(step).map(std::sync::Arc::new))
                    .transpose()?;
                if let Some(test) = test
                    .as_ref()
                    .filter(|test| test.position == crate::kernel::LoopTestPosition::AfterBody)
                {
                    lowered_test = Some(crate::kernel::LoopTestRegion {
                        statement: std::sync::Arc::new(
                            self.lower_kernel_statement(&test.statement)?,
                        ),
                        position: test.position,
                    });
                }
                let (measures, structural) = self.loop_measure_clauses(index, None)?;
                if (!ranking_measures.is_empty() || structural_measure.is_some())
                    && (!measures.is_empty() || structural.is_some())
                {
                    return Err(ClickError::new("duplicate typed-frontend loop measures"));
                }
                let mut checks = invariant_checks.clone();
                checks.extend(self.loop_invariant_checks(index)?);
                let mut effects = effect_checks.clone();
                effects.extend(self.loop_frame_checks(index)?);
                let mut resources = resource_specs.clone();
                resources.extend(self.loop_resource_specs(index));
                ProgramStatement::Loop {
                    test: lowered_test.unwrap_or_else(|| loop_test.clone()),
                    update,
                    invariant: invariant.clone(),
                    invariant_checks: checks,
                    effect_checks: effects,
                    resource_specs: resources,
                    ranking_measures: if measures.is_empty() {
                        ranking_measures.clone()
                    } else {
                        measures
                    },
                    structural_measure: structural.or_else(|| structural_measure.clone()),
                    backedge_target: *backedge_target,
                    natural_exit_target: *natural_exit_target,
                    body: Box::new(body),
                }
            }
            ProgramStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
            } => {
                self.next_statement_index();
                crate::kernel::program_try_catch_int32(
                    self.lower_kernel_statement(try_body)?,
                    binding.clone(),
                    self.lower_kernel_statement(handler)?,
                )
            }
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                self.next_statement_index();
                let body = self.lower_kernel_statement(body)?;
                let cleanup = self.lower_kernel_statement(cleanup)?;
                // The point where the exception continues after the cleanup
                // is numbered as the layout numbers it.
                self.next_statement_index();
                crate::kernel::program_unwind_cleanup(body, cleanup)
            }
            _ => {
                self.next_statement_index();
                statement.clone()
            }
        })
    }

    fn lower_statement(
        &mut self,
        statement: &syntax::CStatement,
        control_targets: &BTreeMap<String, (crate::kernel::ControlTargetId, usize)>,
    ) -> Result<ProgramStatement, ClickError> {
        let previous = self.source_bindings.clone();
        if let Some(bindings) = statement
            .site()
            .and_then(syntax::CSite::get)
            .and_then(|site| site.source_bindings())
        {
            self.source_bindings = Some(bindings.clone());
        }
        let lowered = self.lower_statement_in_scope(statement, control_targets);
        self.source_bindings = previous;
        lowered
    }

    fn lower_statement_in_scope(
        &mut self,
        statement: &syntax::CStatement,
        control_targets: &BTreeMap<String, (crate::kernel::ControlTargetId, usize)>,
    ) -> Result<ProgramStatement, ClickError> {
        Ok(match statement {
            syntax::CStatement::Seq(first, second) => program_seq(
                self.lower_statement(first, control_targets)?,
                self.lower_statement(second, control_targets)?,
            ),
            syntax::CStatement::While {
                test,
                condition,
                body,
                ..
            }
            | syntax::CStatement::DoWhile {
                test,
                condition,
                body,
                ..
            } => {
                let statement_index = self.next_statement_index();
                let loop_index = self.next_loop_index();
                self.begin_loop_record(statement_index, loop_index);
                let post_test = matches!(statement, syntax::CStatement::DoWhile { .. });
                let mut lowered_test = if !post_test {
                    test.as_ref()
                        .map(|test| self.lower_statement(test, control_targets))
                        .transpose()?
                } else {
                    None
                };
                let lowered_body = self.lower_statement(body, control_targets)?;
                if post_test {
                    lowered_test = test
                        .as_ref()
                        .map(|test| self.lower_statement(test, control_targets))
                        .transpose()?;
                }
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_frame_checks(loop_index)?;
                let resource_specs = self.loop_resource_specs(loop_index);
                let (ranking_measures, structural_measure) = self.loop_measure_clauses(
                    loop_index,
                    statement
                        .site()
                        .and_then(syntax::CSite::get)
                        .and_then(|site| site.source_bindings()),
                )?;
                self.end_loop_record(loop_index, true);
                if matches!(statement, syntax::CStatement::DoWhile { .. }) {
                    program_do_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_optional_loop_test(
                        lowered_test,
                        crate::kernel::LoopTestPosition::AfterBody,
                    )
                    .with_loop_resource_specs(resource_specs)
                    .with_loop_ranking_measures(ranking_measures)
                    .with_loop_structural_measure(structural_measure)
                } else {
                    program_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_optional_loop_test(
                        lowered_test,
                        crate::kernel::LoopTestPosition::BeforeBody,
                    )
                    .with_loop_resource_specs(resource_specs)
                    .with_loop_ranking_measures(ranking_measures)
                    .with_loop_structural_measure(structural_measure)
                }
            }
            syntax::CStatement::For {
                test,
                initializer,
                condition,
                step,
                body,
                ..
            } => {
                let lowered_initializer = self.lower_statement(initializer, control_targets)?;
                let statement_index = self.next_statement_index();
                let loop_index = self.next_loop_index();
                self.begin_loop_record(statement_index, loop_index);
                let lowered_test = test
                    .as_ref()
                    .map(|test| self.lower_statement(test, control_targets))
                    .transpose()?;
                let lowered_body = self.lower_statement(body, control_targets)?;
                let lowered_step = self.lower_statement(step, control_targets)?;
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_frame_checks(loop_index)?;
                let resource_specs = self.loop_resource_specs(loop_index);
                let (ranking_measures, structural_measure) = self.loop_measure_clauses(
                    loop_index,
                    statement
                        .site()
                        .and_then(syntax::CSite::get)
                        .and_then(|site| site.source_bindings()),
                )?;
                self.end_loop_record(loop_index, false);
                program_seq(
                    lowered_initializer,
                    program_while_with_invariant_and_effect_checks(
                        condition.to_kernel_expression(),
                        Vec::new(),
                        invariant_checks,
                        effect_checks,
                        lowered_body,
                    )
                    .with_loop_update(lowered_step)
                    .with_optional_loop_test(
                        lowered_test,
                        crate::kernel::LoopTestPosition::BeforeBody,
                    )
                    .with_loop_resource_specs(resource_specs)
                    .with_loop_ranking_measures(ranking_measures)
                    .with_loop_structural_measure(structural_measure),
                )
            }
            syntax::CStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.next_statement_index();
                program_if(
                    condition.to_kernel_expression(),
                    self.lower_statement(then_branch, control_targets)?,
                    self.lower_statement(else_branch, control_targets)?,
                )
            }
            statement => {
                self.next_statement_index();
                statement.to_kernel_statement_with_control_targets(control_targets)
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
    fn loop_resource_specs(&self, loop_index: usize) -> Vec<ResourceSpec> {
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

    fn begin_loop_record(&mut self, statement_index: usize, loop_index: usize) {
        if let Some(records) = &mut self.loop_records {
            debug_assert_eq!(records.len(), loop_index);
            records.push(LoopLoweringRecord {
                statement_index,
                lowered_alone: false,
                quantifiers_after: 0,
                bindings_empty_after: false,
            });
        }
    }

    /// Completes loop `loop_index`'s record once it is lowered; `whole` says
    /// whether its own node is all a lowering of it alone has to visit.
    fn end_loop_record(&mut self, loop_index: usize, whole: bool) {
        let nested = self.loop_index != loop_index + 1;
        let quantifiers_after = self.next_quantifier_variable;
        let bindings_empty_after =
            self.quantified_values.is_empty() && self.algebraic_variables.is_empty();
        if let Some(record) = self
            .loop_records
            .as_mut()
            .and_then(|records| records.get_mut(loop_index))
        {
            record.lowered_alone = whole && !nested;
            record.quantifiers_after = quantifiers_after;
            record.bindings_empty_after = bindings_empty_after;
        }
    }

    /// The loop's declared `decreases` components, in source order.
    ///
    /// The measure travels on the loop head so the back-edge invariant
    /// bundle, the verified loop rule, and the whole-function termination
    /// pass all read the one declared clause rather than agreeing by
    /// coincidence.
    fn loop_ranking_measures(
        &mut self,
        loop_index: usize,
        source_bindings: Option<&syntax::CSourceBindings>,
    ) -> Result<Option<LoopMeasureClauses>, ClickError> {
        let mut measures: Option<LoopMeasureClauses> = None;
        let clauses = self
            .structural_clauses
            .for_loop(loop_index)
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        for clause in &clauses {
            if clause.decreases().is_none() {
                continue;
            }
            let declared =
                match crate::surface::verification::loop_structural_measure_binder(clause) {
                    Some(binder) => LoopMeasureClauses::Structural(binder),
                    None => LoopMeasureClauses::Ranking(self.loop_ranking_components(
                        loop_index,
                        clause,
                        source_bindings,
                    )?),
                };
            match &measures {
                Some(existing) if existing != &declared => {
                    return Err(ClickError::new(format!(
                        "loop {loop_index} has conflicting `decreases` measures"
                    )));
                }
                _ => measures = Some(declared),
            }
        }
        Ok(measures)
    }

    /// One loop's `decreases` components as the loop head carries them.
    ///
    /// A component that reads as a current-state C expression stays one, so
    /// every measure that verifies today lowers to exactly the object it
    /// lowered to before. Anything else is lowered as a loop invariant's
    /// expression is, in the loop-invariant elaboration context: locals stay
    /// C fragments and memory stays `SpecPoint::Current`, so the result
    /// names no state and the kernel is the one that picks the two states to
    /// evaluate it at.
    fn loop_ranking_components(
        &mut self,
        loop_index: usize,
        clause: &StructuralClause,
        source_bindings: Option<&syntax::CSourceBindings>,
    ) -> Result<Vec<crate::kernel::RankingComponent>, ClickError> {
        let Some(measure) = clause.decreases() else {
            return Ok(Vec::new());
        };
        let mut components = Vec::with_capacity(measure.components().len());
        for (component_index, expression) in measure.components().iter().enumerate() {
            let original_expression = expression;
            let resolved = if let Some(bindings) = source_bindings {
                let substitutions = contract_expression_referenced_names(expression)
                    .into_iter()
                    .filter_map(|name| {
                        let (_, binding) = bindings.get(&name)?;
                        Some((
                            name,
                            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                                binding.clone(),
                            )),
                        ))
                    })
                    .collect::<BTreeMap<_, _>>();
                Some(
                    substitute_contract_expression(expression, &substitutions)
                        .map_err(ClickError::new)?,
                )
            } else {
                None
            };
            let expression = resolved.as_ref().unwrap_or(expression);
            // A component that names a proof-local binder was resolved to the
            // value the binder stands for. It is no longer a C expression
            // over this loop's state, so it is lowered as a pure component and
            // named by its written spelling, which is what the termination
            // plan reads from the same clause.
            let written = measure.rewritten_component_source(component_index);
            // A measure is one expression the kernel reads at the iteration's
            // entry state and again at the back-edge state, and ranks the two
            // values against each other. A component that names a state of
            // its own reads the same state twice, so its two values are equal
            // and it can never decrease: `decreases old(m)` used to lower and
            // then leave the back edge permanently open, and a loop-entry
            // `at(...)` reported only that a measure "could not be
            // evaluated". Refuse it here, where the declaration is still
            // readable and the reason can be stated.
            if let Some(fixed) = fixed_measure_state(expression) {
                return Err(ClickError::new(format!(
                    "loop {loop_index} `decreases` component `{}` names the fixed state `{}`; a \
                     termination measure must be a function of the current state alone, because \
                     the kernel evaluates the one declared component at the iteration's entry and \
                     again at the back edge and requires the second value to be smaller. Write the \
                     measure over current values, and use an invariant to relate them to an \
                     earlier state.",
                    crate::surface::verification::termination_measure_source(expression),
                    fixed.spelling()
                )));
            }
            if written.is_none()
                && let Ok(program_expression) = resource_argument_to_program_expression(expression)
            {
                components.push(crate::kernel::RankingComponent::ProgramExpression(
                    program_expression,
                ));
                continue;
            }
            let source = crate::surface::verification::termination_measure_source(
                written.unwrap_or(original_expression),
            );
            let context = SpecElaborationContext::for_loop_invariant(loop_index);
            // A `Nat` measure ranks by its Integer image: `to_integer` is the
            // kernel's checked observation of a structural natural, so the
            // two members are the Integer ones over that image and its
            // nonnegativity is the conversion's own law. Any other algebraic
            // value has no order the ranking members can compare.
            if let Some(ClickType::Algebraic(value_type)) =
                self.contract_expression_click_type(expression, &context)
            {
                if value_type.name() != "Nat" || !value_type.arguments().is_empty() {
                    return Err(ClickError::new(format!(
                        "loop {loop_index} `decreases` component `{source}` has type `{}`, which \
                         has no order a termination measure can rank; a component must be an \
                         int32, unsigned, `Integer`, or `Nat` expression. To rank a loop by the \
                         structure it walks, name its resource binder (`decreases c;`) or a \
                         function of the binder's model into `Integer` or `Nat`",
                        value_type.name()
                    )));
                }
                let observed = ContractExpression::Call {
                    name: "to_integer".to_string(),
                    arguments: vec![expression.clone()],
                };
                let lowered = self
                    .lower_contract_integer_to_spec(&observed, &context)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "loop {loop_index} `decreases` component `{source}`: {message}"
                        ))
                    })?;
                components.push(crate::kernel::RankingComponent::PureInteger {
                    source,
                    expression: lowered,
                });
                continue;
            }
            // A measure whose declared type is `Integer` is lowered in the
            // Integer carrier, by the same rule that picks the carrier for an
            // invariant's operand. Its two obligations are the same two, built
            // over `Integer`.
            if self.contract_expression_is_integer(expression, &context) {
                let lowered = self
                    .lower_contract_integer_to_spec(expression, &context)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "loop {loop_index} `decreases` component `{source}`: {message}"
                        ))
                    })?;
                components.push(crate::kernel::RankingComponent::PureInteger {
                    source,
                    expression: lowered,
                });
                continue;
            }
            let lowered = self
                .lower_contract_expression_to_spec(expression, &context)
                .map_err(|message| {
                    ClickError::new(format!(
                        "loop {loop_index} `decreases` component `{source}`: {message}"
                    ))
                })?;
            components.push(crate::kernel::RankingComponent::Pure {
                source,
                expression: lowered,
            });
        }
        Ok(components)
    }

    /// The function's declared `decreases` measure as its contract interface
    /// carries it, or `None` when the clause is one of the two measures the
    /// termination checker resolves by itself.
    ///
    /// `decreases n` for a C int32 parameter `n`, and a structural resource
    /// measure, keep naming exactly what they named before: those clauses are read by
    /// `program_function_termination_plans` and analysed by the checker, and nothing
    /// about them reaches the interface. Anything else is a pure expression,
    /// lowered here the way a `requires` is, in this same function-contract
    /// context, so it names no state of its own and the kernel is the one
    /// that picks the two states to read it at.
    fn function_recursion_measure(
        &mut self,
        function_block: &FunctionBlock,
        context: &SpecElaborationContext,
    ) -> Result<Vec<crate::kernel::RankingComponent>, ClickError> {
        let components = match function_block.decreases() {
            Some(FunctionDecrease::Numeric(expression)) => std::slice::from_ref(expression),
            Some(FunctionDecrease::Lexicographic(components)) => components.as_slice(),
            _ => return Ok(Vec::new()),
        };
        components
            .iter()
            .map(|expression| {
                self.function_recursion_component(function_block, expression, context)
            })
            .collect()
    }

    /// One component of a function-level expression measure, lowered as a
    /// loop component is.
    fn function_recursion_component(
        &mut self,
        function_block: &FunctionBlock,
        expression: &ContractExpression,
        context: &SpecElaborationContext,
    ) -> Result<crate::kernel::RankingComponent, ClickError> {
        let name = function_block.signature().name();
        // The kernel reads the one declared measure at the function's entry
        // and again at each recursive call, and requires the second value to
        // be smaller. A component that names a state of its own reads one
        // state twice, so it can never decrease -- the same rule the loop
        // slot states, for the same reason.
        if let Some(fixed) = fixed_measure_state(expression) {
            return Err(ClickError::new(format!(
                "function-level `decreases` component `{}` in `{name}` names the fixed state `{}`; \
                 a termination measure must be a function of the current state alone, because the \
                 kernel evaluates the one declared component at the function's entry and again at \
                 each recursive call and requires the second value to be smaller. Write the \
                 measure over current values, and use a `requires` clause to relate them to an \
                 earlier state.",
                crate::surface::verification::termination_measure_source(expression),
                fixed.spelling()
            )));
        }
        // The carrier is chosen exactly as the loop slot chooses it: an
        // `Integer`-typed measure lowers into the Integer carrier and owes the
        // same two obligations there.
        if self.contract_expression_is_integer(expression, context) {
            let lowered = self
                .lower_contract_integer_to_spec(expression, context)
                .map_err(|message| {
                    ClickError::new(format!(
                        "function-level `decreases` component `{}` in `{name}`: {message}",
                        crate::surface::verification::termination_measure_source(expression)
                    ))
                })?;
            return Ok(crate::kernel::RankingComponent::PureInteger {
                source: crate::surface::verification::termination_measure_source(expression),
                expression: lowered,
            });
        }
        let lowered = self
            .lower_contract_expression_to_spec(expression, context)
            .map_err(|message| {
                ClickError::new(format!(
                    "function-level `decreases` component `{}` in `{name}`: {message}",
                    crate::surface::verification::termination_measure_source(expression)
                ))
            })?;
        Ok(crate::kernel::RankingComponent::Pure {
            source: crate::surface::verification::termination_measure_source(expression),
            expression: lowered,
        })
    }

    /// The loop head's declared measure, split into the two clauses the
    /// kernel loop statement carries.
    fn loop_measure_clauses(
        &mut self,
        loop_index: usize,
        source_bindings: Option<&syntax::CSourceBindings>,
    ) -> Result<(Vec<crate::kernel::RankingComponent>, Option<String>), ClickError> {
        Ok(
            match self.loop_ranking_measures(loop_index, source_bindings)? {
                Some(LoopMeasureClauses::Ranking(components)) => (components, None),
                Some(LoopMeasureClauses::Structural(binder)) => (Vec::new(), Some(binder)),
                None => (Vec::new(), None),
            },
        )
    }

    fn loop_invariant_checks(
        &mut self,
        loop_index: usize,
    ) -> Result<Vec<LoopInvariantCheck>, ClickError> {
        self.structural_clauses
            .for_loop(loop_index)
            .into_iter()
            .flat_map(StructuralClause::items)
            .enumerate()
            .map(|(item_index, item)| {
                let proposition = item.proposition().clone();
                Ok(LoopInvariantCheck::new(
                    self.click_proposition_to_spec_proposition(
                        &proposition,
                        &SpecElaborationContext::for_loop_invariant(loop_index),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "loop {loop_index} {}: {message}",
                            item.title(item_index)
                        ))
                    })?,
                    Some(format!(
                        "loop {loop_index} {} entry",
                        item.title(item_index)
                    )),
                    Some(format!(
                        "loop {loop_index} {} preservation",
                        item.title(item_index)
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
        enum Frame<'a> {
            Visit(&'a ClickProposition),
            BuildAnd,
            BuildOr,
            BuildImplies,
        }

        if !matches!(
            proposition,
            ClickProposition::And(..) | ClickProposition::Or(..) | ClickProposition::Implies(..)
        ) {
            #[cfg(test)]
            tests::PROPOSITION_VISITS.with(|visits| visits.set(visits.get() + 1));
            return self.click_proposition_to_spec_proposition_one(proposition, environment);
        }

        let mut frames = vec![Frame::Visit(proposition)];
        let mut expanded = Vec::new();
        while let Some(frame) = frames.pop() {
            match frame {
                Frame::Visit(proposition) => {
                    #[cfg(test)]
                    tests::PROPOSITION_VISITS.with(|visits| visits.set(visits.get() + 1));
                    match proposition {
                        ClickProposition::And(left, right) => {
                            frames.push(Frame::BuildAnd);
                            frames.push(Frame::Visit(right));
                            frames.push(Frame::Visit(left));
                        }
                        ClickProposition::Or(left, right) => {
                            frames.push(Frame::BuildOr);
                            frames.push(Frame::Visit(right));
                            frames.push(Frame::Visit(left));
                        }
                        ClickProposition::Implies(left, right) => {
                            frames.push(Frame::BuildImplies);
                            frames.push(Frame::Visit(right));
                            frames.push(Frame::Visit(left));
                        }
                        proposition => {
                            expanded.push(self.click_proposition_to_spec_proposition_one(
                                proposition,
                                environment,
                            )?)
                        }
                    }
                }
                Frame::BuildAnd => {
                    let right = expanded
                        .pop()
                        .expect("elaborated conjunction right operand");
                    let left = expanded.pop().expect("elaborated conjunction left operand");
                    expanded.push(SpecProposition::And(Box::new(left), Box::new(right)));
                }
                Frame::BuildOr => {
                    let right = expanded
                        .pop()
                        .expect("elaborated disjunction right operand");
                    let left = expanded.pop().expect("elaborated disjunction left operand");
                    expanded.push(SpecProposition::Or(Box::new(left), Box::new(right)));
                }
                Frame::BuildImplies => {
                    let right = expanded
                        .pop()
                        .expect("elaborated implication right operand");
                    let left = expanded.pop().expect("elaborated implication left operand");
                    expanded.push(SpecProposition::Implies(Box::new(left), Box::new(right)));
                }
            }
        }
        Ok(expanded
            .pop()
            .expect("elaborated proposition should have one root"))
    }

    #[inline(never)]
    fn click_proposition_to_spec_proposition_one(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::Value(expression) => {
                self.lower_proposition_value(expression, environment)
            }
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
            | ClickProposition::ResourceViewable { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::Defined { .. } => {
                self.lower_atomic_proposition_to_spec(proposition, environment)
            }
        }
    }

    fn lower_proposition_value(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        if let Some(reduced) = lambdas::reduce_head(expression)? {
            return self.lower_proposition_value(&reduced, environment);
        }
        // A written `true` or `false` is that truth value, not `literal ==
        // true`.
        if let Some(value) = crate::surface::bool_literal_value(expression) {
            return Ok(SpecProposition::Truth(value));
        }
        match expression {
            ContractExpression::Call { name, arguments }
                if self
                    .spec_definitions
                    .functions
                    .get(name)
                    .is_some_and(|definition| {
                        definition.return_type() == &ClickType::Proposition
                    }) =>
            {
                let definition = self
                    .spec_definitions
                    .functions
                    .get(name)
                    .filter(|definition| definition.return_type() == &ClickType::Proposition)
                    .cloned()
                    .ok_or("a proposition call must return Prop")?;
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, environment)?;
                let body = lambdas::specialize_call(&definition, arguments)?
                    .ok_or("a Prop function needs a concrete body")?;
                self.lower_proposition_value(&body, environment)
            }
            ContractExpression::Proposition(proposition) => {
                self.click_proposition_to_spec_proposition(proposition, environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_proposition_to_spec(
                &ClickProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(ClickProposition::Value(expression.as_ref().clone())),
                },
                environment,
            ),
            ContractExpression::Let {
                name,
                click_type,
                value,
                body,
            } => {
                if self.contract_expression_click_type_in_scope(value, environment, &mut Vec::new())
                    == Some(ClickType::Proposition)
                {
                    let substituted = substitute_contract_expression(
                        body,
                        &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
                    )?;
                    return self.lower_proposition_value(&substituted, environment);
                }
                let mut body_environment = environment.clone();
                body_environment.values.remove(name);
                body_environment.integer_values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                if *click_type == Some(ClickType::Integer)
                    || (click_type.is_none()
                        && self.contract_expression_is_integer(value, environment))
                {
                    let value = self.lower_contract_integer_to_spec(value, environment)?;
                    body_environment.integer_values.insert(name.clone(), value);
                } else if matches!(click_type, Some(ClickType::Algebraic(_)))
                    || contract_expression_is_algebraic(
                        value,
                        self.spec_definitions.functions,
                        environment,
                        &mut Vec::new(),
                    )
                {
                    let value = self.lower_contract_algebraic_to_spec(value, environment)?;
                    body_environment
                        .algebraic_values
                        .insert(name.clone(), value);
                } else {
                    let mut value = self.lower_contract_expression_to_spec(value, environment)?;
                    if let Some(ClickType::Program(ty)) = click_type {
                        value = value.at_machine_type(ty.to_kernel_type());
                    }
                    body_environment.values.insert(name.clone(), value);
                }
                self.lower_proposition_value(body, &body_environment)
            }
            _ if self.contract_expression_click_type_in_scope(
                expression,
                environment,
                &mut Vec::new(),
            ) == Some(ClickType::Program(InterfaceType::Bool)) =>
            {
                self.click_proposition_to_spec_proposition(
                    &bool_truth(expression.clone()),
                    environment,
                )
            }
            _ => Err("a proposition application must produce Prop or Bool".into()),
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
                if let Some(retained_state) = self.point_environment(selector, environment)? {
                    return self
                        .click_proposition_to_spec_proposition(proposition, &retained_state);
                }
                match self.resolve_visit_selector(selector, environment)? {
                    ResolvedProgramPoint::Current => {
                        self.click_proposition_to_spec_proposition(proposition, environment)
                    }
                    ResolvedProgramPoint::FunctionEntry => {
                        let old_environment = environment
                            .old_state(&self.entry_values, &self.entry_state.program_point())?;
                        self.click_proposition_to_spec_proposition(proposition, &old_environment)
                    }
                    _ => Err("`at(...)` propositions are proof-script states".to_string()),
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
                click_type,
                name,
                written_name,
                body,
            } => {
                let display_name = name.kernel_name();
                let _ = written_name;
                let variable = allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
                let mut body_environment = environment.clone();
                body_environment.integer_values.remove(name);
                body_environment.values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                if *click_type == ClickType::Integer {
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
                if let ClickType::Algebraic(application) = click_type {
                    let algebraic_type = self.cached_algebraic_kernel_type(application)?;
                    body_environment.algebraic_values.insert(
                        name.clone(),
                        SpecAlgebraicExpression {
                            algebraic_type: algebraic_type.clone(),
                            node: SpecAlgebraicExpressionNode::Variable(variable),
                        },
                    );
                    let body =
                        self.click_proposition_to_spec_proposition(body, &body_environment)?;
                    return Ok(SpecProposition::ForAllAlgebraic {
                        name: display_name.clone(),
                        variable,
                        algebraic_type,
                        body: Box::new(body),
                    });
                }
                let program_type = click_type
                    .interface_type()
                    .ok_or("only C quantifier binders are currently supported")?
                    .to_kernel_type();
                let value = match program_type {
                    program_type
                        if crate::kernel::MachineIntegerType::from_program_type(program_type)
                            .is_some() =>
                    {
                        crate::kernel::MachineIntegerType::from_program_type(program_type)
                            .expect("machine integer")
                            .symbolic_value(variable)
                    }
                    program_type if program_type.is_pointer() => {
                        if matches!(program_type, ProgramType::FunctionPointer(_)) {
                            ProgramValue::typed_pointer(
                                Address::symbolic_function(variable),
                                program_type,
                            )
                        } else {
                            ProgramValue::typed_pointer(Address::symbolic(variable), program_type)
                        }
                    }
                    _ => {
                        return Err(
                            "only machine-integer and pointer binders are supported".to_string()
                        );
                    }
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
                if program_type == ProgramType::Int32 {
                    Ok(SpecProposition::ForAllInt32 {
                        name: display_name.clone(),
                        variable,
                        body: Box::new(body),
                    })
                } else if let Some(integer_type) =
                    crate::kernel::MachineIntegerType::from_program_type(program_type)
                {
                    Ok(SpecProposition::ForAllMachineInteger {
                        name: display_name.clone(),
                        variable,
                        integer_type,
                        body: Box::new(body),
                    })
                } else {
                    Ok(SpecProposition::ForAllPointer {
                        name: display_name.clone(),
                        variable,
                        program_type,
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
                click_type,
                name,
                written_name,
                body,
            } => {
                let display_name = written_name
                    .as_ref()
                    .map(crate::kernel::BindingName::from)
                    .unwrap_or_else(|| name.kernel_name());
                let variable = allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
                let mut body_environment = environment.clone();
                body_environment.integer_values.remove(name);
                body_environment.values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                if *click_type == ClickType::Integer {
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
                if let ClickType::Algebraic(application) = click_type {
                    let algebraic_type = self.cached_algebraic_kernel_type(application)?;
                    body_environment.algebraic_values.insert(
                        name.clone(),
                        SpecAlgebraicExpression {
                            algebraic_type: algebraic_type.clone(),
                            node: SpecAlgebraicExpressionNode::Variable(variable),
                        },
                    );
                    let body =
                        self.click_proposition_to_spec_proposition(body, &body_environment)?;
                    return Ok(SpecProposition::ExistsAlgebraic {
                        name: display_name.clone(),
                        variable,
                        algebraic_type,
                        body: Box::new(body),
                    });
                }
                let program_type = click_type
                    .interface_type()
                    .ok_or("only C quantifier binders are currently supported")?
                    .to_kernel_type();
                let value = match program_type {
                    program_type
                        if crate::kernel::MachineIntegerType::from_program_type(program_type)
                            .is_some() =>
                    {
                        crate::kernel::MachineIntegerType::from_program_type(program_type)
                            .expect("machine integer")
                            .symbolic_value(variable)
                    }
                    program_type if program_type.is_pointer() => {
                        if matches!(program_type, ProgramType::FunctionPointer(_)) {
                            ProgramValue::typed_pointer(
                                Address::symbolic_function(variable),
                                program_type,
                            )
                        } else {
                            ProgramValue::typed_pointer(Address::symbolic(variable), program_type)
                        }
                    }
                    _ => {
                        return Err(
                            "only machine-integer and pointer binders are supported".to_string()
                        );
                    }
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
                if program_type == ProgramType::Int32 {
                    Ok(SpecProposition::ExistsInt32 {
                        name: display_name.clone(),
                        variable,
                        body: Box::new(body),
                    })
                } else if let Some(integer_type) =
                    crate::kernel::MachineIntegerType::from_program_type(program_type)
                {
                    Ok(SpecProposition::ExistsMachineInteger {
                        name: display_name.clone(),
                        variable,
                        integer_type,
                        body: Box::new(body),
                    })
                } else {
                    Ok(SpecProposition::ExistsPointer {
                        name: display_name.clone(),
                        variable,
                        program_type,
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
                let display_item = item.kernel_name();
                let _ = written_item;
                // A range with a `uint64` endpoint ranges over `uint64` values,
                // as a range fold's does: its item is a `size_t` index.
                let wide = self.range_bounds_are_uint64(start, end, environment);
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
                let item_carrier = if wide {
                    ProgramValue::UInt64(MachineTerm::Variable(variable))
                } else {
                    ProgramValue::Int32(MachineTerm::Variable(variable))
                };
                let item_value = SpecExpression::Value(item_carrier.clone());
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(item.clone(), item_carrier);
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
                let body = Box::new(SpecProposition::Implies(Box::new(range), Box::new(body)));
                Ok(if wide {
                    SpecProposition::ForAllMachineInteger {
                        name: display_item.clone(),
                        variable,
                        integer_type: crate::kernel::MachineIntegerType::UInt64,
                        body,
                    }
                } else {
                    SpecProposition::ForAllInt32 {
                        name: display_item.clone(),
                        variable,
                        body,
                    }
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
                let display_item = item.kernel_name();
                let _ = written_item;
                // A range with a `uint64` endpoint ranges over `uint64` values,
                // as a range fold's does: its item is a `size_t` index.
                let wide = self.range_bounds_are_uint64(start, end, environment);
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
                let item_carrier = if wide {
                    ProgramValue::UInt64(MachineTerm::Variable(variable))
                } else {
                    ProgramValue::Int32(MachineTerm::Variable(variable))
                };
                let item_value = SpecExpression::Value(item_carrier.clone());
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(item.clone(), item_carrier);
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
                let body = Box::new(SpecProposition::And(Box::new(range), Box::new(body)));
                Ok(if wide {
                    SpecProposition::ExistsMachineInteger {
                        name: display_item.clone(),
                        variable,
                        integer_type: crate::kernel::MachineIntegerType::UInt64,
                        body,
                    }
                } else {
                    SpecProposition::ExistsInt32 {
                        name: display_item.clone(),
                        variable,
                        body,
                    }
                })
            }
            _ => unreachable!("proposition dispatched to the wrong lowering helper"),
        }
    }

    fn lower_pure_parameter_argument_to_spec(
        &mut self,
        parameter: &FunctionParameter,
        argument: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        // Lower the borrowed argument once: wrapping its surface tree first
        // would clone every nested call's subtree.
        let value = self.lower_contract_expression_to_spec(argument, environment)?;
        Ok(match pure_function_parameter_conversion(parameter) {
            Some((target, crate::kernel::IntegerCastMode::PointerCoercion)) => {
                SpecExpression::PointerCoercion(Box::new(value), target)
            }
            Some((target, _)) => SpecExpression::Cast(Box::new(value), target),
            None => value,
        })
    }

    #[inline(never)]
    fn lower_predicate_call_proposition_to_spec(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::PredicateCall { name, arguments } => {
                if let Some(definition) = self
                    .spec_definitions
                    .functions
                    .get(name)
                    .filter(|definition| definition.return_type() == &ClickType::Proposition)
                    .cloned()
                {
                    let definition = self.instantiate_click_function_for_call(
                        &definition,
                        arguments,
                        environment,
                    )?;
                    let body = lambdas::specialize_call(&definition, arguments)?
                        .ok_or("a Prop function needs a concrete body")?;
                    return self.lower_proposition_value(&body, environment);
                }

                if let Some(kind) = crate::kernel::TerminationAtomKind::from_spelling(name) {
                    let scope = self.spec_definitions.termination_scope
                        .ok_or("termination propositions are available only inside `termination by` proofs")?;
                    let function = match (kind, arguments.as_slice()) {
                        (crate::kernel::TerminationAtomKind::Callbacks, []) => "",
                        (_, [ContractExpression::Binding(name)])
                            if kind != crate::kernel::TerminationAtomKind::Callbacks =>
                        {
                            name
                        }
                        _ => return Err(format!("invalid arguments to `{name}`")),
                    };
                    let Proposition::Predicate { name, arguments } = scope.atom(kind, function)?
                    else {
                        unreachable!()
                    };
                    debug_assert!(matches!(arguments.as_slice(), [Term::ExecutionState(_)]));
                    return Ok(SpecProposition::Predicate {
                        name,
                        arguments: vec![],
                        resource_state_dependent: false,
                    });
                }
                if name == "held" {
                    let [mutex] = arguments.as_slice() else {
                        return Err(format!(
                            "held expects one mutex pointer, got {}",
                            arguments.len()
                        ));
                    };
                    return Ok(SpecProposition::MutexHeld(Box::new(
                        self.lower_contract_expression_to_spec(mutex, environment)?,
                    )));
                }
                if name == "little_endian" {
                    if !arguments.is_empty() {
                        return Err("little_endian expects no arguments".into());
                    }
                    return Ok(SpecProposition::Predicate {
                        resource_state_dependent: false,
                        name: crate::kernel::LITTLE_ENDIAN_PREDICATE_NAME.into(),
                        arguments: vec![],
                    });
                }
                if name == "same_object" {
                    let [left, right] = arguments.as_slice() else {
                        return Err(format!(
                            "same_object expects two pointer arguments, got {}",
                            arguments.len()
                        ));
                    };
                    return Ok(SpecProposition::Predicate {
                        resource_state_dependent: false,
                        name: crate::kernel::SAME_OBJECT_PREDICATE_NAME.to_string(),
                        arguments: vec![
                            SpecPredicateArgument::Value(
                                self.lower_contract_expression_to_spec(left, environment)?,
                            ),
                            SpecPredicateArgument::Value(
                                self.lower_contract_expression_to_spec(right, environment)?,
                            ),
                        ],
                    });
                }
                if let Some(signature) = self.spec_definitions.predicates.contract_signature(name) {
                    let value_count = self
                        .spec_definitions
                        .predicates
                        .contract_definition(name)
                        .map_or(0, |definition| definition.value_parameters().len());
                    let Some((function, values)) = arguments
                        .split_first()
                        .filter(|(_, values)| values.len() == value_count)
                    else {
                        return Err(if value_count == 0 {
                            format!("contract `{name}` expects one function-pointer argument")
                        } else {
                            format!(
                                "contract `{name}` expects a function pointer and its {value_count} value parameter(s)"
                            )
                        });
                    };
                    let function = match contract_expression_function_address(function) {
                        Some(target) => SpecExpression::ProgramExpression(
                            ProgramExpression::Value(ProgramValue::typed_pointer(
                                Address::function(
                                    self.spec_definitions
                                        .predicates
                                        .function_execution_name(target)
                                        .to_string(),
                                ),
                                signature.to_kernel_type(),
                            )),
                        ),
                        None => self.lower_contract_expression_to_spec(function, environment)?,
                    };
                    let mut contract_arguments = vec![SpecPredicateArgument::Value(function)];
                    for value in values {
                        contract_arguments.push(SpecPredicateArgument::Value(
                            self.lower_contract_expression_to_spec(value, environment)?,
                        ));
                    }
                    return Ok(SpecProposition::Predicate {
                        resource_state_dependent: false,
                        name: FunctionContract::predicate_name_for(name),
                        arguments: contract_arguments,
                    });
                }
                let definition = self
                    .spec_definitions
                    .predicates
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
                    let mut predicate_environment = SpecElaborationContext::with_current_point(
                        environment.current_point.clone(),
                    );
                    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
                        match parameter.click_type() {
                            ClickType::Proposition | ClickType::Function { .. } => {
                                return Err(
                                    "specification function parameters are not supported yet"
                                        .into(),
                                );
                            }
                            ClickType::Resource => {
                                return Err(
                                    "Resource predicate parameters are not supported".into()
                                );
                            }
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
                            ClickType::Program(_) | ClickType::CObjectPointer { .. }
                                if parameter_is_click_array_ref(parameter) =>
                            {
                                predicate_environment.array_refs.insert(
                                    parameter.name().to_string(),
                                    self.lower_array_ref_to_spec(argument, environment)?,
                                );
                            }
                            ClickType::Program(_) | ClickType::CObjectPointer { .. } => {
                                predicate_environment.values.insert(
                                    parameter.name().to_string(),
                                    self.lower_pure_parameter_argument_to_spec(
                                        parameter,
                                        argument,
                                        environment,
                                    )?,
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
                        let expected_element_type = click_array_element_type(
                            parameter.interface_type(),
                        )
                        .ok_or_else(|| {
                            format!(
                                "predicate `{}` parameter `{}` is not an array-ref parameter",
                                definition.name(),
                                parameter.name()
                            )
                        })?;
                        let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                        if !crate::surface::validation::array_ref_elements_compatible(
                            array_ref.element_type,
                            expected_element_type,
                        ) {
                            return Err(format!(
                                "predicate `{}` parameter `{}` expects {:?} array elements, got {:?}",
                                definition.name(),
                                parameter.name(),
                                expected_element_type,
                                array_ref.element_type
                            ));
                        }
                        // A character array of the other signedness is
                        // passed as the predicate's own element pointer, so
                        // the instance is the one its callers and callees
                        // name; the bytes read the same either way.
                        let pointer = if array_ref.element_type == expected_element_type {
                            array_ref.pointer
                        } else {
                            SpecExpression::Cast(
                                Box::new(array_ref.pointer),
                                expected_element_type.pointer_to().ok_or_else(|| {
                                    format!(
                                        "predicate `{}` parameter `{}` has no element pointer type",
                                        definition.name(),
                                        parameter.name()
                                    )
                                })?,
                            )
                        };
                        lowered_arguments.push(SpecPredicateArgument::ArrayRef {
                            point: array_ref.point,
                            pointer,
                        });
                    } else {
                        lowered_arguments.push(SpecPredicateArgument::Value(
                            self.lower_pure_parameter_argument_to_spec(
                                parameter,
                                argument,
                                environment,
                            )?,
                        ));
                    }
                }
                Ok(SpecProposition::Predicate {
                    resource_state_dependent: self
                        .spec_definitions
                        .predicates
                        .resource_state_dependent
                        .contains(name),
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
                if let (Some(left_element), Some(right_element)) = (
                    self.contract_pointer_element_type(left, environment),
                    self.contract_pointer_element_type(right, environment),
                ) && left_element != right_element
                {
                    return Err(format!(
                        "incompatible pointer comparison: {:?} pointer and {:?} pointer; use a checked byte-view cast to compare byte views",
                        left_element, right_element
                    ));
                }
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
                let has_algebraic = self.enum_program_value_type(left, environment).is_some()
                    || self.enum_program_value_type(right, environment).is_some()
                    || contract_expression_is_algebraic(
                        left,
                        self.spec_definitions.functions,
                        environment,
                        &mut Vec::new(),
                    )
                    || contract_expression_is_algebraic(
                        right,
                        self.spec_definitions.functions,
                        environment,
                        &mut Vec::new(),
                    )
                    || self.generic_call_returns_algebraic(left, environment)
                    || self.generic_call_returns_algebraic(right, environment);
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
                    syntax::CFloatClassification::Finite => FloatClassification::Finite,
                    syntax::CFloatClassification::Infinite => FloatClassification::Infinite,
                    syntax::CFloatClassification::Zero => FloatClassification::Zero,
                    syntax::CFloatClassification::Subnormal => FloatClassification::Subnormal,
                    syntax::CFloatClassification::Nan => FloatClassification::Nan,
                },
            }),
            ClickProposition::Separate { left, right } => Ok(SpecProposition::ResourceSeparate {
                left: self.lower_resource_subject_to_spec(left, environment)?,
                right: self.lower_resource_subject_to_spec(right, environment)?,
            }),
            ClickProposition::ResourceViewable { resource } => {
                Ok(SpecProposition::ResourceViewable {
                    point: environment.current_point.clone(),
                    resource: self.lower_resource_subject_to_spec(resource, environment)?,
                })
            }
            ClickProposition::Contains { parent, child } => Ok(SpecProposition::ResourceContains {
                parent: self.lower_resource_subject_to_spec(parent, environment)?,
                child: self.lower_resource_subject_to_spec(child, environment)?,
            }),
            ClickProposition::Loadable { segment } => {
                let segment_environment = self.spec_segment_environment(segment, environment)?;
                Ok(SpecProposition::MemoryLoadable {
                    point: segment_environment.current_point.clone(),
                    base: self
                        .lower_contract_segment_base_to_spec(&segment.base, &segment_environment)?,
                    start: self
                        .lower_program_expression_to_spec(&segment.start, &segment_environment)?,
                    end: self
                        .lower_program_expression_to_spec(&segment.end, &segment_environment)?,
                    element_width: self
                        .contract_segment_element_width(segment, &segment_environment)?,
                })
            }
            ClickProposition::Defined { expression } => {
                let mut checked_environment = environment.clone();
                checked_environment.checking_definedness = true;
                Ok(SpecProposition::Defined(
                    self.lower_contract_expression_to_spec(expression, &checked_environment)?,
                ))
            }
            _ => unreachable!("non-atomic proposition dispatched to leaf lowering"),
        }
    }

    /// The value a fixed state gives one resource field.
    ///
    /// Only an explicit `at(...)` state fixes one. That state names a
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
        // Every field access reaches here, whichever of the three lowering
        // paths it takes, and here both halves of `c.rank` are in hand: the
        // reader's own name for the instance, and the kernel identity the
        // fresh field variables were registered under. One insert per access,
        // so that a refusal downstream can spell a model-field variable
        // instead of printing it (`crate::kernel::model_fields`).
        crate::kernel::model_fields::register_instance_spelling(access.identity, &access.owner);
        if let Some(state) = environment.reference_state.as_ref() {
            return state
                .resource_instance_at_path(access.identity, &access.children)
                .and_then(|instance| {
                    crate::kernel::record_transport_field(instance, access.field_index);
                    instance.fields().get(access.field_index)
                })
                .map(crate::kernel::ResourceFieldValue::into_native)
                .map(Some)
                .ok_or_else(|| {
                    format!(
                        "resource instance `{}` is not owned at this state",
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
        let mut depth = 0;
        let mut current = expression;
        while let ContractExpression::Add(left, right) = current {
            if !matches!(right.as_ref(), ContractExpression::IntegerLiteral(_)) {
                break;
            }
            depth += 1;
            current = left;
        }
        if depth > 128 && matches!(current, ContractExpression::IntegerLiteral(_)) {
            return false;
        }
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

    /// Whether a range's endpoints make its item a `uint64`: one endpoint
    /// is a `uint64`, as for a range fold.
    fn range_bounds_are_uint64(
        &self,
        start: &ContractExpression,
        end: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> bool {
        [start, end].into_iter().any(|bound| {
            matches!(
                self.contract_expression_click_type(bound, environment),
                Some(ClickType::Program(InterfaceType::UInt64(_)))
            ) || matches!(bound, ContractExpression::ProgramExpression(ProgramExpression::Variable(name))
                    if self.c_variable_type(name) == Some(ProgramType::UInt64))
                || matches!(bound, ContractExpression::ProgramExpression(ProgramExpression::Value(value))
                    if value.program_type() == ProgramType::UInt64)
                // A written cast, `n as uint64`, has the type it names.
                || matches!(
                    generics::explicit_cast_click_type(bound),
                    Some(ClickType::Program(InterfaceType::UInt64(_)))
                )
        })
    }

    /// The declared C type of a parameter or local named in a clause, from
    /// its typed entry value or the live declaration state.
    fn c_variable_type(&self, name: impl Into<crate::kernel::BindingName>) -> Option<ProgramType> {
        let name = self.source_binding(name.into());
        if name == crate::kernel::CONTRACT_RESULT {
            return Some(self.result_type);
        }
        if name.unresolved_name().is_none() {
            return name.program_type();
        }
        name.metadata_in(&self.program_parameter_types)
            .copied()
            .or_else(|| {
                name.metadata_in(&self.entry_values)
                    .map(ProgramValue::program_type)
            })
            .or_else(|| {
                self.entry_state
                    .locals()
                    .get(&name)
                    .map(|value| value.program_type())
            })
            .or_else(|| {
                self.local_type_state
                    .and_then(|state| state.local_object_type(&name))
            })
    }

    fn contract_expression_click_type_in_scope(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
        lexical_bindings: &mut Vec<(SurfaceBinder, Option<ClickType>)>,
    ) -> Option<ClickType> {
        if let Some(id) = expression.generated_binder() {
            if let Some((_, ty)) = lexical_bindings
                .iter()
                .rev()
                .find(|(name, _)| name == &SurfaceBinder::Generated(id))
            {
                return ty.clone();
            }
            if environment.integer_values.contains_key(&id) {
                return Some(ClickType::Integer);
            }
            if let Some(value) = environment.algebraic_values.get(&id) {
                return Some(generics::click_type_from_algebraic_value_type(
                    &value.algebraic_type.value_type(),
                ));
            }
            return environment
                .values
                .get(&id)
                .and_then(spec_expression_click_type);
        }

        match expression {
            ContractExpression::IntegerContext(_) => Some(ClickType::Integer),

            ContractExpression::Lambda {
                parameters, result, ..
            } => Some(lambdas::signature(parameters, result)),
            ContractExpression::Apply { function, .. } => match self
                .contract_expression_click_type_in_scope(function, environment, lexical_bindings)?
            {
                ClickType::Function { result, .. } => Some(*result),
                _ => None,
            },

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
                        Some(ClickType::Program(InterfaceType::Int32))
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
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => {
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
            ContractExpression::ProgramBinding(name) => lexical_bindings
                .iter()
                .rev()
                .find_map(|(binding, click_type)| (binding == name).then(|| click_type.clone()))
                .flatten()
                .or_else(|| {
                    environment
                        .values
                        .get(name)
                        .and_then(spec_expression_click_type)
                }),
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
                    algebraic_kernel_type(self.spec_definitions.functions, &application)
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
                        Some(ClickType::Integer) | Some(ClickType::Program(_))
                    )
                {
                    return None;
                }
                result_type
            }
            // An Integer conditional: Integer branches, or one Integer branch
            // and an unsuffixed numeral, which takes its type. Any other
            // conditional keeps its C lowering, so it is not typed here.
            ContractExpression::If {
                then_branch,
                else_branch,
                ..
            } => {
                let then_type = self.contract_expression_click_type_in_scope(
                    then_branch,
                    environment,
                    lexical_bindings,
                );
                let else_type = self.contract_expression_click_type_in_scope(
                    else_branch,
                    environment,
                    lexical_bindings,
                );
                let integer_or_numeral = |branch_type: &Option<ClickType>, branch| {
                    *branch_type == Some(ClickType::Integer)
                        || (branch_type.is_none()
                            && is_unsuffixed_integer_literal_expression(branch))
                };
                ((then_type == Some(ClickType::Integer) || else_type == Some(ClickType::Integer))
                    && integer_or_numeral(&then_type, then_branch)
                    && integer_or_numeral(&else_type, else_branch))
                .then_some(ClickType::Integer)
            }
            ContractExpression::Call { name, .. }
                if name == "to_integer" || is_integer_truncation(name) =>
            {
                Some(ClickType::Integer)
            }
            ContractExpression::Call { name, .. } => self
                .spec_definitions
                .functions
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
        if let Some(id) = expression.generated_binder()
            && let Some(value) = environment.integer_values.get(&id)
        {
            return Ok(value.clone());
        }

        if let Some(reduced) = lambdas::reduce_head(expression)? {
            return self.lower_contract_integer_to_spec(&reduced, environment);
        }
        use crate::kernel::SpecIntegerExpression;
        check_integer_lowering_work(1)?;
        match expression {
            ContractExpression::IntegerContext(value) => {
                return self.lower_contract_integer_to_spec(value, environment);
            }
            ContractExpression::Old(inner) => {
                let old_environment =
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                return self.lower_contract_integer_to_spec(inner, &old_environment);
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                if let Some(retained_state) = self.point_environment(selector, environment)? {
                    return self.lower_contract_integer_to_spec(expression, &retained_state);
                }
                // `at(function.entry, e)` is `old(e)` and the current point
                // is `e`, as for C values and sequences.
                return match self.resolve_visit_selector(selector, environment)? {
                    ResolvedProgramPoint::Current => {
                        self.lower_contract_integer_to_spec(expression, environment)
                    }
                    ResolvedProgramPoint::FunctionEntry => {
                        let old_environment = environment
                            .old_state(&self.entry_values, &self.entry_state.program_point())?;
                        self.lower_contract_integer_to_spec(expression, &old_environment)
                    }
                    ResolvedProgramPoint::LoopEntry(_) => {
                        Err("Integer values require a recorded program point".to_string())
                    }
                };
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
                        AlgebraicValueType::Program(value_type)
                        | AlgebraicValueType::ObjectPointer(value_type, _) => {
                            bind_match_program_value(&mut body_environment, binding, *value_type);
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
                                        binding.kernel_name(),
                                    ),
                                },
                            );
                        }
                        AlgebraicValueType::Integer => {
                            body_environment.values.remove(binding);
                            body_environment.algebraic_values.remove(binding);
                            let variable =
                                allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
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
                    bindings: arm
                        .bindings
                        .iter()
                        .map(SurfaceBinder::kernel_name)
                        .collect(),
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
        if let ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } = expression
        {
            return Ok(SpecIntegerExpression::If {
                condition: Box::new(
                    self.click_proposition_to_spec_proposition(condition, environment)?,
                ),
                then_branch: Box::new(
                    self.lower_contract_integer_to_spec(then_branch, environment)?,
                ),
                else_branch: Box::new(
                    self.lower_contract_integer_to_spec(else_branch, environment)?,
                ),
            });
        }
        // The proof parser preserves a variable reference as a C fragment
        // until contextual typing identifies it as an Integer.  Resolve it
        // through the active scoped environment so fold accumulator and
        // captured Integer references retain their preallocated kernel terms.
        if let ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) = expression
            && let Some(value) = environment.integer_values.get(name)
        {
            return Ok(value.clone());
        }
        match expression {
            ContractExpression::Call { name, arguments } if is_integer_truncation(name) => {
                let (left, right) = integer_truncation_arguments(name, arguments)?;
                let left = self.lower_contract_integer_to_spec(left, environment)?;
                let right = self.lower_contract_integer_to_spec(right, environment)?;
                // Only a pure, nonzero constant divisor removes the domain check.
                // Deferred operand effects must survive surrounding simplification.
                if let (SpecIntegerExpression::Term(a), SpecIntegerExpression::Term(b)) =
                    (&left, &right)
                    && b.as_const()
                        .is_some_and(|b| b != &num_bigint::BigInt::from(0))
                {
                    check_integer_lowering_work(
                        integer_root_work(a).saturating_mul(integer_root_work(b)),
                    )?;
                    return construct_integer_operation(
                        if name == "truncating_quotient" {
                            crate::kernel::KernelIntegerOperator::TruncatingQuotient
                        } else {
                            crate::kernel::KernelIntegerOperator::TruncatingRemainder
                        },
                        vec![a.clone(), b.clone()],
                    );
                }
                Ok(if name == "truncating_quotient" {
                    SpecIntegerExpression::TruncatingQuotient(Box::new(left), Box::new(right))
                } else {
                    SpecIntegerExpression::TruncatingRemainder(Box::new(left), Box::new(right))
                })
            }
            ContractExpression::Call { name, arguments } if name != "to_integer" => {
                let definition = self
                    .spec_definitions
                    .functions
                    .get(name)
                    .ok_or_else(|| format!("unknown function `{name}`"))?
                    .clone();
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, environment)?;
                if let Some(body) = lambdas::specialize_call(&definition, arguments)? {
                    return self.lower_contract_integer_to_spec(&body, environment);
                }

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
                            crate::kernel::SharedPureApplication::intern(
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
                // An Integer is its own exact value.
                if self.contract_expression_is_integer(argument, environment) {
                    return self.lower_contract_integer_to_spec(argument, environment);
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
                    let destination =
                        crate::kernel::MachineIntegerType::from_program_type(value.program_type())
                            .ok_or_else(|| {
                                "to_integer expects a signed or unsigned machine integer"
                                    .to_string()
                            })?;
                    let (crate::kernel::integer_c_value!(bits)) = value.numeric_value() else {
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
                if let Some(literal) = integer_literal_spelling(expression) {
                    return self.lower_contract_integer_to_spec(
                        &ContractExpression::IntegerLiteral(literal),
                        environment,
                    );
                }
                let inner = self.lower_contract_integer_to_spec(inner, environment)?;
                match inner {
                    SpecIntegerExpression::Term(term) => {
                        check_integer_lowering_work(integer_root_work(&term))?;
                        construct_integer_operation(
                            crate::kernel::KernelIntegerOperator::Negate,
                            vec![term],
                        )
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
                let accumulator_variable =
                    allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
                let item_variable =
                    allocate_quantifier_variable(&mut self.next_quantifier_variable)?;
                // Bare numerals inherit the range's index carrier. Only an
                // explicitly mathematical operand selects Integer indices.
                fn integer_index_expression(
                    expression: &ContractExpression,
                    environment: &SpecElaborationContext,
                    functions: &ClickFunctionEnvironment,
                ) -> bool {
                    if let Some(id) = expression.generated_binder() {
                        return environment.integer_values.contains_key(&id);
                    }
                    match expression {
                        ContractExpression::IntegerContext(_) => true,
                        ContractExpression::Binding(name)
                        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                            crate::kernel::BindingName::Named(name),
                        )) => environment.integer_values.contains_key(name),
                        ContractExpression::ResourceField(access) => {
                            access.click_type == Some(ClickType::Integer)
                        }
                        ContractExpression::Call { name, .. } => {
                            is_integer_truncation(name)
                                || functions.get(name).is_some_and(|function| {
                                    function.return_type() == &ClickType::Integer
                                })
                        }
                        ContractExpression::Add(left, right)
                        | ContractExpression::Subtract(left, right)
                        | ContractExpression::Multiply(left, right) => {
                            integer_index_expression(left, environment, functions)
                                || integer_index_expression(right, environment, functions)
                        }
                        _ => false,
                    }
                }
                let integer_index = [start, end].into_iter().any(|expression| {
                    integer_index_expression(
                        expression,
                        environment,
                        self.spec_definitions.functions,
                    )
                });
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
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                // A range with a `uint64` endpoint ranges over `uint64`
                // values, and its item has that type: the index type of the
                // code a model function describes. A nonnegative literal at
                // the other endpoint is that number.
                // An argument bound to a `uint64` parameter arrives as a
                // cast to the parameter's type.
                let is_uint64 = |expression: &SpecExpression| {
                    matches!(expression, SpecExpression::Cast(_, ProgramType::UInt64))
                        || matches!(
                            spec_expression_click_type(expression),
                            Some(ClickType::Program(
                                crate::languages::interface::InterfaceType::UInt64(_)
                            ))
                        )
                };
                let as_uint64 = |expression: SpecExpression| match &expression {
                    SpecExpression::Value(ProgramValue::Int32(bits32_constant!(value)))
                        if constant_u32(*value) <= i32::MAX as u32 =>
                    {
                        SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(
                            u64::from(constant_u32(*value)),
                        )))
                    }
                    _ => expression,
                };
                let (start, end, unsigned64) = if is_uint64(&start) || is_uint64(&end) {
                    let (start, end) = (as_uint64(start), as_uint64(end));
                    let unsigned64 = is_uint64(&start) && is_uint64(&end);
                    (start, end, unsigned64)
                } else {
                    (start, end, false)
                };
                let item_term = MachineTerm::Variable(item_variable);
                body_environment.values.insert(
                    item.clone(),
                    SpecExpression::Value(if unsigned64 {
                        ProgramValue::UInt64(item_term)
                    } else {
                        ProgramValue::Int32(item_term)
                    }),
                );
                let body = self.lower_contract_integer_to_spec(body, &body_environment)?;
                let (start, end) = (Box::new(start), Box::new(end));
                Ok(SpecIntegerExpression::RangeFold {
                    index: if unsigned64 {
                        crate::kernel::SpecIntegerRangeFoldIndex::UInt64 { start, end }
                    } else {
                        crate::kernel::SpecIntegerRangeFoldIndex::Int32 { start, end }
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
            // A `let` of a C value around Integer arithmetic, as
            // specification arithmetic makes `entry + 1`: the body reads the
            // name as that C value.
            ContractExpression::Let {
                name,
                click_type: click_type @ (None | Some(ClickType::Program(_))),
                value,
                body,
            } if !self.contract_expression_is_integer(value, environment) => {
                let mut value = self.lower_contract_expression_to_spec(value, environment)?;
                // A typed `let`'s value is at its declared type (G2).
                if let Some(ClickType::Program(interface_type)) = click_type {
                    value = value.at_machine_type(interface_type.to_kernel_type());
                }
                let mut body_environment = environment.clone();
                body_environment.integer_values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                body_environment.values.insert(name.clone(), value);
                self.lower_contract_integer_to_spec(body, &body_environment)
            }
            _ => lower_contract_integer_to_spec(expression, &environment.integer_values),
        }
    }

    /// Lower a field whose base pointer is named in another state. The
    /// base expression supplies the pointer value from that state, while
    /// the field itself is read from the surrounding environment's memory.
    /// This is the meaning of `old(p->kid)->payload`.
    fn lower_program_point_field_to_spec(
        &mut self,
        base: &ContractExpression,
        lowered: &ProgramExpression,
        offset_bytes: u32,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let pointer = self.lower_contract_expression_to_spec(base, environment)?;
        let pointer = if offset_bytes == 0 {
            pointer
        } else {
            SpecExpression::PointerOffset {
                pointer: Box::new(pointer),
                elements: Box::new(SpecExpression::Value(int32(offset_bytes))),
                byte_width: 1,
            }
        };
        match lowered {
            ProgramExpression::TypedLoad {
                value_type:
                    ProgramType::Int32Array(_)
                    | ProgramType::UInt32Array(_)
                    | ProgramType::UInt8Array(_)
                    | ProgramType::Int128Array(_)
                    | ProgramType::Int64Array(_)
                    | ProgramType::UInt128Array(_)
                    | ProgramType::UInt64Array(_),
                ..
            } => Ok(pointer),
            ProgramExpression::TypedLoad { value_type, .. } => Ok(SpecExpression::MemoryLoad {
                point: environment.current_point.clone(),
                pointer: Box::new(pointer),
                value_type: *value_type,
            }),
            ProgramExpression::Load(pointer_expression) => Ok(SpecExpression::MemoryLoad {
                point: environment.current_point.clone(),
                pointer: Box::new(pointer),
                value_type: self
                    .program_expression_array_element_type(pointer_expression, environment)
                    .unwrap_or(ProgramType::Int32),
            }),
            _ => Ok(pointer),
        }
    }

    fn lower_contract_expression_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        if let Some(reduced) = lambdas::reduce_head(expression)? {
            return self.lower_contract_expression_to_spec(&reduced, environment);
        }
        let mut operands = Vec::new();
        let mut current = expression;
        while let ContractExpression::Add(left, right) = current {
            if !matches!(right.as_ref(), ContractExpression::IntegerLiteral(_)) {
                return self.lower_contract_expression_to_spec_one(expression, environment);
            }
            operands.push(right.as_ref());
            current = left;
        }
        if !operands.is_empty()
            && self
                .contract_pointer_element_type(current, environment)
                .is_none()
            && self
                .call_pointer_element_width(current, environment)?
                .is_none()
        {
            operands.push(current);
            let mut lowered = self.lower_contract_expression_to_spec_one(
                operands.pop().expect("the additive base is present"),
                environment,
            )?;
            for operand in operands.into_iter().rev() {
                let right = self.lower_contract_expression_to_spec_one(operand, environment)?;
                lowered = SpecExpression::Add(Box::new(lowered), Box::new(right));
            }
            return Ok(lowered);
        }
        self.lower_contract_expression_to_spec_one(expression, environment)
    }

    fn lower_contract_expression_to_spec_one(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        if let Some(id) = expression.generated_binder() {
            if let Some(value) = environment.values.get(&id) {
                return Ok(value.clone());
            }
            return Err(format!("unbound specification binder `{id}`"));
        }

        if let Some((region, accesses)) = region_result_read(expression)
            && let Some(retained_states) = self.retained_states
        {
            let index = retained_states.result_region_index(region)?;
            // Ordinary pointer results retain their usual indexing and member reads.
            if retained_states
                .source_layout
                .as_ref()
                .is_some_and(|layout| layout.is_aggregate_result(index))
            {
                return self.lower_region_result_read(region, &accesses, environment);
            }
        }
        if let Some((region, name, accesses)) = region_parameter_read(expression) {
            return self.lower_region_parameter_read(region, name, &accesses, environment);
        }
        match expression {
            ContractExpression::IntegerContext(_) => {
                Err("an Integer context is not a C-valued expression".into())
            }

            ContractExpression::Proposition(_) => Err("a Prop is not a C scalar value".into()),
            ContractExpression::Resource(_) => Err("a Resource descriptor is not a C value".into()),
            ContractExpression::Lambda { .. } => {
                Err("a specification lambda must be applied to produce a scalar".into())
            }
            ContractExpression::Apply { .. } => {
                let reduced = lambdas::reduce_head(expression)?
                    .ok_or("application needs a concrete lambda")?;
                self.lower_contract_expression_to_spec(&reduced, environment)
            }

            ContractExpression::CUnary { operand, lowered } => {
                let value = self.lower_contract_expression_to_spec(operand, environment)?;
                match lowered {
                    ProgramExpression::Cast {
                        target_type,
                        pointee_struct,
                        integer_mode,
                        ..
                    } => {
                        if *target_type == ProgramType::UInt8Pointer
                            && pointee_struct.is_none()
                            && !matches!(
                                self.contract_expression_click_type(operand, environment),
                                Some(ClickType::Program(
                                    InterfaceType::Int64(_) | InterfaceType::UInt64(_)
                                ))
                            )
                            && !self
                                .contract_pointer_element_type(operand, environment)
                                .is_some_and(|element| {
                                    !element.is_pointer() && element.byte_width() > 0
                                })
                        {
                            return Err(
                                "native byte-view cast expects a scalar object pointer operand"
                                    .to_string(),
                            );
                        }
                        Ok(
                            if *integer_mode == crate::kernel::IntegerCastMode::PointerCoercion {
                                SpecExpression::PointerCoercion(Box::new(value), *target_type)
                            } else if *integer_mode
                                == crate::kernel::IntegerCastMode::ResultConversion
                            {
                                // A pure function's body is at its result
                                // type (G2).
                                SpecExpression::Cast(
                                    Box::new(value.at_machine_type(*target_type)),
                                    *target_type,
                                )
                            } else {
                                SpecExpression::Cast(Box::new(value), *target_type)
                            },
                        )
                    }
                    ProgramExpression::PointerOffsetBytes { bytes, .. } => {
                        Ok(SpecExpression::PointerOffset {
                            pointer: Box::new(value),
                            elements: Box::new(SpecExpression::Value(int32(*bytes))),
                            byte_width: 1,
                        })
                    }
                    ProgramExpression::Subobject { width, .. } => Ok(SpecExpression::Subobject {
                        pointer: Box::new(value),
                        width: *width,
                    }),
                    ProgramExpression::TypedLoad { value_type, .. } => {
                        Ok(SpecExpression::MemoryLoad {
                            point: environment.current_point.clone(),
                            pointer: Box::new(value),
                            value_type: *value_type,
                        })
                    }
                    ProgramExpression::Load(_) => Ok(SpecExpression::MemoryLoad {
                        point: environment.current_point.clone(),
                        pointer: Box::new(value),
                        value_type: self.contract_array_element_type(operand, environment),
                    }),
                    ProgramExpression::AddressOf(_)
                    | ProgramExpression::CheckedObjectAddress(_) => {
                        // Rebuild from the authoritative surface operand,
                        // including values already bound into a postcondition.
                        // Keep the address operation and selected member bounds.
                        let values = if environment.contract_result_in_scope {
                            BTreeMap::from([(
                                "result".to_string(),
                                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                                    crate::kernel::CONTRACT_RESULT,
                                )),
                            )])
                        } else {
                            BTreeMap::new()
                        };
                        let rebound = substitute_contract_expression_in(
                            expression,
                            &ContractSubstitutions::for_contract_result(&values),
                        )?;
                        let lowered = contract_expression_as_program_expression(&rebound)
                            .ok_or("address operand is not a C expression")?;
                        // Substitution has resolved the built-in result while
                        // retaining explicit C bindings such as `program::result`.
                        let mut rebound_environment = environment.clone();
                        rebound_environment.contract_result_in_scope = false;
                        self.lower_program_expression_to_spec(&lowered, &rebound_environment)
                    }
                    _ => Err("invalid C unary operation".to_string()),
                }
            }

            ContractExpression::MethodCall { method, .. } => Err(format!(
                "the method `{method}` was not resolved by its receiver's type"
            )),
            // A subslice's length, `end - start`, owes `start <= end <= len`
            // where it is evaluated, as Rust panics otherwise.
            ContractExpression::Call { name, arguments }
                if name == crate::surface::RUST_SUBSLICE_LEN
                    && let [start, end, len] = arguments.as_slice() =>
            {
                let at_most = |left: &ContractExpression, right: &ContractExpression| {
                    ClickProposition::Comparison {
                        left: left.clone(),
                        operator: ComparisonOperator::LessEqual,
                        right: right.clone(),
                    }
                };
                // A subslice from the start, `s[..b]`, has length `b` itself,
                // so it is the slice `slice::from_raw_parts(s.as_ptr(), b)`
                // is, and owes only `b <= len`.
                let from_start = matches!(start, ContractExpression::IntegerLiteral(text) if text == "0")
                    || matches!(
                        start,
                        ContractExpression::ProgramExpression(ProgramExpression::Value(_))
                    ) && crate::surface::diagnostics::describe_contract_expression(start)
                        == "0u64";
                let (requirement, value) = if from_start {
                    (at_most(end, len), end.clone())
                } else {
                    (
                        ClickProposition::And(
                            Box::new(at_most(start, end)),
                            Box::new(at_most(end, len)),
                        ),
                        ContractExpression::Subtract(
                            Box::new(end.clone()),
                            Box::new(start.clone()),
                        ),
                    )
                };
                Ok(SpecExpression::Requires {
                    requirement: Box::new(
                        self.click_proposition_to_spec_proposition(&requirement, environment)?,
                    ),
                    value: Box::new(self.lower_contract_expression_to_spec(&value, environment)?),
                })
            }
            ContractExpression::Call { name, arguments }
                if integer_conversion_target(name).is_some() =>
            {
                let argument = integer_conversion_argument(name, arguments)?;
                let destination = crate::kernel::MachineIntegerType::from_program_type(
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
                    ProgramValue::Int32(MachineTerm::constant(value as u32))
                } else if value <= i64::MAX as u64 {
                    ProgramValue::Int64(MachineTerm::int64_constant(value as i64))
                } else {
                    ProgramValue::UInt64(MachineTerm::uint64_constant(value))
                };
                Ok(SpecExpression::Value(value))
            }
            ContractExpression::ResourceField(access) => {
                let Some(ClickType::Program(interface_type)) = &access.click_type else {
                    return Err("expected a scalar resource field".into());
                };
                if let Some(value) = self.fixed_resource_field(access, environment)? {
                    let AlgebraicValue::Program(value) = value else {
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
                    program_type: interface_type.to_kernel_type(),
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
                            SpecAlgebraicValue::Program(field) => {
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
                                AlgebraicValueType::Program(value_type)
                                | AlgebraicValueType::ObjectPointer(value_type, _) => {
                                    bind_match_program_value(
                                        &mut body_environment,
                                        binding,
                                        *value_type,
                                    );
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
                                                binding.kernel_name(),
                                            ),
                                        },
                                    );
                                }
                                AlgebraicValueType::Integer => {
                                    body_environment.values.remove(binding);
                                    body_environment.algebraic_values.remove(binding);
                                    let variable = allocate_quantifier_variable(
                                        &mut self.next_quantifier_variable,
                                    )?;
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
                            bindings: arm
                                .bindings
                                .iter()
                                .map(SurfaceBinder::kernel_name)
                                .collect(),
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
            ContractExpression::Field {
                base,
                lowered,
                offset_bytes,
                ..
            } if contract_expression_has_explicit_program_result_reference(base) => {
                self.lower_program_point_field_to_spec(base, lowered, *offset_bytes, environment)
            }
            ContractExpression::ArrayIndex {
                base,
                indexes,
                dimensions,
                lowered,
            } if contract_expression_has_explicit_program_result_reference(base)
                || indexes
                    .iter()
                    .any(contract_expression_has_explicit_program_result_reference) =>
            {
                let pointer = self.lower_contract_expression_to_spec(base, environment)?;
                let mut offset = None;
                for (index, expression) in indexes.iter().enumerate() {
                    let stride =
                        dimensions[index + 1..]
                            .iter()
                            .try_fold(1u32, |stride, dimension| {
                                stride
                                    .checked_mul(*dimension)
                                    .ok_or_else(|| "array stride overflow".to_string())
                            })?;
                    let mut term =
                        self.lower_contract_expression_to_spec(expression, environment)?;
                    if stride != 1 {
                        term = SpecExpression::Multiply(
                            Box::new(term),
                            Box::new(SpecExpression::Value(int32(stride))),
                        );
                    }
                    offset = Some(match offset {
                        None => term,
                        Some(previous) => SpecExpression::Add(Box::new(previous), Box::new(term)),
                    });
                }
                let offset = offset.ok_or_else(|| "array access requires an index".to_string())?;
                match lowered {
                    ProgramExpression::Index(lowered_base, _) => {
                        let value_type = self
                            .program_expression_array_element_type(lowered_base, environment)
                            .unwrap_or(ProgramType::Int32);
                        Ok(SpecExpression::MemoryLoad {
                            point: environment.current_point.clone(),
                            pointer: Box::new(SpecExpression::PointerOffset {
                                pointer: Box::new(pointer),
                                elements: Box::new(offset),
                                byte_width: value_type.byte_width(),
                            }),
                            value_type,
                        })
                    }
                    ProgramExpression::Add(lowered_base, stride) => {
                        let ProgramExpression::Multiply(_, width) = stride.as_ref() else {
                            return Err("invalid struct array stride".to_string());
                        };
                        Ok(SpecExpression::PointerOffset {
                            pointer: Box::new(pointer),
                            elements: Box::new(SpecExpression::Multiply(
                                Box::new(offset),
                                Box::new(
                                    self.lower_program_expression_to_spec(width, environment)?,
                                ),
                            )),
                            byte_width: self
                                .program_expression_array_element_width(lowered_base, environment)
                                .unwrap_or(1),
                        })
                    }
                    _ => Err("invalid array access lowering".to_string()),
                }
            }
            ContractExpression::QualifiedC {
                lowered: expression,
                ..
            }
            | ContractExpression::ProgramExpression(expression)
            | ContractExpression::ArrayIndex {
                lowered: expression,
                ..
            } => self.lower_program_expression_to_spec(expression, environment),
            ContractExpression::Field {
                base,
                lowered,
                offset_bytes,
                ..
            } if matches!(
                base.as_ref(),
                ContractExpression::Old(_) | ContractExpression::At { .. }
            ) =>
            {
                self.lower_program_point_field_to_spec(base, lowered, *offset_bytes, environment)
            }
            ContractExpression::Field {
                base,
                field,
                lowered,
                ..
            } => {
                if let Some(ClickType::Program(interface_type)) =
                    self.contract_expression_click_type(base, environment)
                    && !interface_type.is_pointer()
                {
                    return Err(format!(
                        "cannot read field `{field}` of `{}`: `{}` has no fields",
                        diagnostics::describe_contract_expression(base),
                        describe_interface_type(interface_type),
                    ));
                }
                self.lower_program_expression_to_spec(lowered, environment)
            }
            ContractExpression::Binding(name) => {
                if environment.algebraic_values.contains_key(name) {
                    return Err(format!(
                        "algebraic binding `{name}` is not valid in a C-valued expression"
                    ));
                }
                self.lower_program_expression_to_spec(
                    &ProgramExpression::Variable((name.clone()).into()),
                    environment,
                )
            }
            ContractExpression::ProgramBinding(name) => {
                self.lower_program_binding_to_spec(name, environment)
            }
            ContractExpression::ResourceCount(resource) => {
                let ResourceClause::Declared {
                    name, arguments, ..
                } = resource.as_ref()
                else {
                    return Err("`count(...)` expects a declared resource".to_string());
                };
                if environment.reference_state.is_some() {
                    return Err("`count(R(p))` at a recorded state is unavailable".to_string());
                }
                if arguments.is_empty()
                    || matches!(arguments[0], ContractExpression::ResourceWildcard)
                    || (arguments
                        .iter()
                        .skip(1)
                        .any(|argument| matches!(argument, ContractExpression::ResourceWildcard))
                        && arguments.iter().skip(1).any(|argument| {
                            !matches!(argument, ContractExpression::ResourceWildcard)
                        }))
                {
                    return Err(
                        "count requires R(anchor), R(anchor, _, ...), or an exact member"
                            .to_string(),
                    );
                }
                let arguments = arguments
                    .iter()
                    .map(|argument| match argument {
                        ContractExpression::ResourceWildcard => Ok(None),
                        argument => self
                            .lower_contract_expression_to_spec(argument, environment)
                            .map(Some),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let count = SpecExpression::CountedResourceCount {
                    name: name.clone(),
                    arguments,
                };
                // A count named at the function entry is the entry's
                // population, which the kernel evaluates at the entry state.
                Ok(if environment.at_function_entry {
                    SpecExpression::LoopEntryState(Box::new(count))
                } else {
                    count
                })
            }
            ContractExpression::ResourceWildcard => {
                Err("`_` is only valid inside a `count(...)` resource pattern".to_string())
            }
            ContractExpression::RegionAllocation(region) => {
                let retained_states = self
                    .retained_states
                    .ok_or("`.allocation` requires a function execution")?;
                Ok(SpecExpression::Value(
                    retained_states.region_allocation(region)?,
                ))
            }
            ContractExpression::RegionResult(region) => {
                let retained_states = self
                    .retained_states
                    .ok_or("`.result` names a region of a function body being executed")?;
                Ok(SpecExpression::Value(
                    retained_states
                        .region_result_value_at(region, environment.call_result_point.as_ref())?,
                ))
            }
            ContractExpression::RegionParameter { region, name } => Err(format!(
                "`{}.parameter({name})` is the call's copy of an aggregate argument; read a field of it, as `{}.parameter({name}).field`",
                diagnostics::describe_code_region_ref(region),
                diagnostics::describe_code_region_ref(region),
            )),

            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
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
                    return Ok(SpecExpression::Value(ProgramValue::Int32(
                        MachineTerm::constant(0u32.wrapping_sub(value as u32)),
                    )));
                }
                Ok(SpecExpression::Negate(Box::new(
                    self.lower_contract_expression_to_spec(expression, environment)?,
                )))
            }
            // Arithmetic on a pointer offsets it by whole elements, as C does.
            ContractExpression::Add(left, right) => {
                // A pointer-valued pure call steps by its result's pointee,
                // `slice::as_ptr(s) + k`, on either side.
                for (pointer, elements) in [(left, right), (right, left)] {
                    if let Some(element_width) =
                        self.call_pointer_element_width(pointer, environment)?
                    {
                        return Ok(SpecExpression::PointerOffset {
                            pointer: Box::new(
                                self.lower_contract_expression_to_spec(pointer, environment)?,
                            ),
                            elements: Box::new(
                                self.lower_contract_expression_to_spec(elements, environment)?,
                            ),
                            byte_width: element_width,
                        });
                    }
                }
                if let Some(element_width) = self.contract_pointer_element_width(left, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_contract_expression_to_spec(left, environment)?,
                        ),
                        elements: Box::new(
                            self.lower_contract_expression_to_spec(right, environment)?,
                        ),
                        byte_width: element_width,
                    });
                }
                if let Some(element_width) = self.contract_pointer_element_width(right, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_contract_expression_to_spec(right, environment)?,
                        ),
                        elements: Box::new(
                            self.lower_contract_expression_to_spec(left, environment)?,
                        ),
                        byte_width: element_width,
                    });
                }
                Ok(SpecExpression::Add(
                    Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                    Box::new(self.lower_contract_expression_to_spec(right, environment)?),
                ))
            }
            ContractExpression::Subtract(left, right) => {
                if let Some(element_width) = self.contract_pointer_element_width(left, environment)
                    && self
                        .contract_pointer_element_width(right, environment)
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
                        byte_width: element_width,
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
            ContractExpression::RustShiftLeft(left, right) => Ok(SpecExpression::RustShiftLeft(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::RustShiftRight(left, right) => Ok(SpecExpression::RustShiftRight(
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
                let projection = match base.as_ref() {
                    ContractExpression::Field { lowered, .. }
                    | ContractExpression::ArrayIndex { lowered, .. }
                    | ContractExpression::ProgramExpression(lowered) => {
                        aggregate_projection_root(lowered)
                    }
                    _ => None,
                }
                .filter(|parameter| {
                    matches!(environment.current_point, SpecPoint::Current)
                        && environment.current_loop_entry.is_none()
                        && (parameter
                            .named()
                            .is_some_and(|parameter| self.aggregate_parameters.contains(parameter))
                            || self
                                .entry_state
                                .locals()
                                .aggregate_layout(parameter)
                                .is_some())
                });
                let mut projection_environment = environment.clone();
                if let Some(parameter) = projection
                    && let Some(name) = parameter.named()
                {
                    projection_environment.values.insert(
                        name.to_owned(),
                        SpecExpression::ProgramExpression(ProgramExpression::Variable(
                            parameter.clone(),
                        )),
                    );
                }
                let array_ref = self.lower_array_ref_to_spec(base, &projection_environment)?;
                let index = self.lower_contract_expression_to_spec(index, environment)?;
                let pointer = Box::new(SpecExpression::PointerOffset {
                    pointer: Box::new(array_ref.pointer),
                    elements: Box::new(index),
                    byte_width: array_ref.element_type.byte_width(),
                });
                if let Some(parameter) = projection {
                    Ok(SpecExpression::AggregateFieldValue {
                        parameter: parameter.clone(),
                        pointer,
                        value_type: array_ref.element_type,
                    })
                } else {
                    Ok(SpecExpression::MemoryLoad {
                        point: array_ref.point,
                        pointer,
                        value_type: array_ref.element_type,
                    })
                }
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
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let initial = self.lower_contract_expression_to_spec(initial, environment)?;
                // C-valued subfolds can occur inside Integer expressions, so
                // guard the kernel's carrier here as well as in validation.
                let interface_type = |expression: &SpecExpression| match expression {
                    SpecExpression::Cast(_, ty) | SpecExpression::PointerCoercion(_, ty) => Some(
                        ClickType::Program(generics::interface_type_from_program_type(*ty)),
                    ),
                    _ => spec_expression_click_type(expression),
                };
                let unsupported = |expression: &SpecExpression| {
                    interface_type(expression)
                        .is_some_and(|ty| ty != ClickType::Program(InterfaceType::Int32))
                };
                if unsupported(&start) || unsupported(&end) {
                    return Err("C-valued range fold requires int32 bounds; uint64 bounds require an Integer accumulator".to_string());
                }
                if unsupported(&initial) {
                    return Err("C-valued range fold requires an int32 accumulator; other C accumulator types are not supported".to_string());
                }
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    accumulator.clone(),
                    SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        (accumulator.clone()).into(),
                    )),
                );
                body_environment.values.insert(
                    item.clone(),
                    SpecExpression::ProgramExpression(ProgramExpression::Variable(
                        (item.clone()).into(),
                    )),
                );
                Ok(SpecExpression::RangeFold {
                    start: Box::new(start),
                    end: Box::new(end),
                    initial: Box::new(initial),
                    accumulator: accumulator.kernel_name(),
                    item: item.kernel_name(),
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
                    self.spec_definitions.functions,
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
                let mut value = self.lower_contract_expression_to_spec(value, environment)?;
                // A typed `let`'s value is at its declared type (G2).
                if let Some(ClickType::Program(interface_type)) = click_type {
                    value = value.at_machine_type(interface_type.to_kernel_type());
                }
                if let (Some(ClickType::Program(interface_type)), SpecExpression::Value(fixed)) =
                    (click_type, &value)
                    && !program_value_matches_click_type(fixed, *interface_type)
                {
                    return Err(format!(
                        "let binding `{name}` evaluated to `{}` of type `{}`, which does not match the declared type `{}`",
                        crate::surface::diagnostics::describe_program_value(
                            fixed,
                            ParameterBinding::default()
                        ),
                        crate::kernel::program_type_spelling(fixed.program_type()),
                        crate::surface::validation::describe_interface_type(*interface_type)
                    ));
                }
                let mut body_environment = environment.clone();
                let reference = SpecExpression::ProgramExpression(ProgramExpression::Variable(
                    name.kernel_name(),
                ));
                let reference = if matches!(name, SurfaceBinder::Generated(_)) {
                    match click_type
                        .as_ref()
                        .and_then(ClickType::interface_type)
                        .or_else(|| {
                            spec_expression_click_type(&value).and_then(|ty| ty.interface_type())
                        })
                        .map(|ty| ty.to_kernel_type())
                    {
                        Some(ty) => SpecExpression::Cast(Box::new(reference), ty),
                        None => reference,
                    }
                } else {
                    reference
                };
                body_environment.values.insert(name, reference);
                Ok(SpecExpression::Let {
                    name: name.kernel_name(),
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

    /// The Rust enum type of C name `name`, a parameter, local or `result`
    /// that holds an enum's value.
    fn enum_program_name_type(
        &self,
        name: &str,
        environment: &SpecElaborationContext,
    ) -> Option<crate::kernel::TypeParameterName> {
        match self.program_name_type(name, environment)? {
            ProgramType::Parameter(enum_type) if crate::surface::holds_spec_value(enum_type) => {
                Some(enum_type)
            }
            _ => None,
        }
    }

    /// The C type of C name `name`, a parameter, local or `result`, unless a
    /// spec binding shadows it.
    fn program_name_type(
        &self,
        name: impl Into<crate::kernel::BindingName>,
        environment: &SpecElaborationContext,
    ) -> Option<ProgramType> {
        let name = self.source_binding(name.into());
        if name == crate::kernel::CONTRACT_RESULT {
            return Some(self.result_type);
        }
        if matches!(name, crate::kernel::BindingName::Generated(_)) {
            return environment
                .values
                .get(&name)
                .and_then(spec_expression_click_type)
                .and_then(|ty| ty.interface_type())
                .map(|ty| ty.to_kernel_type());
        }
        if name.unresolved_name().is_none() {
            return name.program_type();
        }
        if name.named_in(&environment.algebraic_values).is_some() {
            return None;
        }
        if name.is_named("result") {
            Some(self.result_type)
        } else {
            name.metadata_in(&self.program_parameter_types)
                .copied()
                .or_else(|| {
                    name.metadata_in(&self.entry_values)
                        .map(ProgramValue::program_type)
                        .or_else(|| {
                            self.local_type_state
                                .and_then(|state| state.locals().get(&name))
                                .map(|value| value.program_type())
                        })
                        // A name bound to a value in this context: a fixed state's
                        // local, including one that keeps an enum in memory.
                        .or_else(|| match name.named_in(&environment.values)? {
                            SpecExpression::Value(value @ ProgramValue::Parameter(_)) => {
                                Some(value.program_type())
                            }
                            _ => None,
                        })
                })
        }
    }

    /// The Rust enum type of the value `expression` names: a C name that
    /// holds one, or `*r` for a reference `r` to one.
    fn enum_program_value_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Option<crate::kernel::TypeParameterName> {
        match expression {
            ContractExpression::Binding(name)
            | ContractExpression::ProgramBinding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => self.enum_program_name_type(name, environment),
            ContractExpression::ProgramExpression(ProgramExpression::Load(pointer)) => {
                let ProgramExpression::Variable(name) = pointer.as_ref() else {
                    return None;
                };
                match self.program_name_type(name, environment)? {
                    ProgramType::ParameterPointer(enum_type)
                        if crate::surface::holds_spec_value(enum_type) =>
                    {
                        Some(enum_type)
                    }
                    _ => None,
                }
            }
            ContractExpression::Old(inner) => self.enum_program_value_type(inner, environment),
            // The enum value a call returned.
            ContractExpression::RegionResult(region) => {
                match self
                    .retained_states?
                    .region_result_value_at(region, environment.call_result_point.as_ref())
                    .ok()?
                {
                    ProgramValue::Parameter(term) => {
                        let enum_type = crate::kernel::TypeParameterName::of(&term.algebraic_type);
                        crate::surface::holds_spec_value(enum_type).then_some(enum_type)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn lower_contract_algebraic_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecAlgebraicExpression, String> {
        if let Some(id) = expression.generated_binder()
            && let Some(value) = environment.algebraic_values.get(&id)
        {
            return Ok(value.clone());
        }

        if let Some(reduced) = lambdas::reduce_head(expression)? {
            return self.lower_contract_algebraic_to_spec(&reduced, environment);
        }
        if let Some(enum_type) = self.enum_program_value_type(expression, environment) {
            return Ok(SpecAlgebraicExpression {
                algebraic_type: enum_type.algebraic_type(),
                node: SpecAlgebraicExpressionNode::ProgramValue(Box::new(
                    self.lower_contract_expression_to_spec(expression, environment)?,
                )),
            });
        }
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
                    // A named state has only the value it holds; the
                    // function entry also has its symbolic projection.
                    Some(_) if environment.reference_state.is_some() => {
                        return Err("only entry-bound symbolic resource fields support fixed states in this slice".into());
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
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => environment
                .algebraic_values
                .get(name)
                .cloned()
                .ok_or_else(|| format!("`{name}` is not an algebraic binding in this scope")),
            ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments,
            } => {
                if algebraic_type.arguments.is_empty()
                    && !algebraic_type.rigid
                    && let Some(definition) = self
                        .spec_definitions
                        .functions
                        .algebraic_type_definitions
                        .get(&algebraic_type.name)
                    && !definition.type_parameters().is_empty()
                {
                    return Err(crate::surface::validation::unapplied_constructor_message(
                        definition.name(),
                        variant,
                        definition.type_parameters(),
                    ));
                }
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
                        // A pointer-typed payload takes the C null pointer
                        // constant, exactly as a resource argument and a pure
                        // call's argument do: `RbTree::Node(node, 0, ...)` is
                        // how a model says this node is the root. Without the
                        // field's declared type the literal lowers as an
                        // `int32` zero and the constructor denotes no value.
                        AlgebraicValueType::Program(interface_type)
                        | AlgebraicValueType::ObjectPointer(interface_type, _)
                            if interface_type.is_pointer()
                                && matches!(
                                    argument,
                                    ContractExpression::IntegerLiteral(text) if text == "0"
                                ) =>
                        {
                            Ok(SpecAlgebraicValue::Program(SpecExpression::Value(
                                crate::kernel::ProgramValue::typed_pointer(
                                    crate::kernel::Address::null(),
                                    *interface_type,
                                ),
                            )))
                        }
                        // An integer literal is a value of its field's type,
                        // as a C initializer's is. Without the type it lowers
                        // at the narrowest width that holds it, so `2` in an
                        // `int64` field is an `int32` and the constructor
                        // compares with no `Seq<int64>` value. A constant of
                        // literals, `3 - 1`, is the literal it denotes. A
                        // literal the type cannot hold is refused, never
                        // wrapped.
                        AlgebraicValueType::Program(interface_type)
                            if crate::kernel::MachineIntegerType::from_program_type(*interface_type).is_some()
                                && integer_constant_spelling(argument).is_some() =>
                        {
                            let text = integer_constant_spelling(argument)
                                .expect("the guard matched an integer constant");
                            let ty = crate::kernel::MachineIntegerType::from_program_type(*interface_type)
                                .expect("the guard matched an integer type");
                            crate::kernel::MachineIntegerConstant::parse_decimal(ty.format(), &text)
                                .and_then(|value| ty.constant_value(value))
                                .map(|value| SpecAlgebraicValue::Program(SpecExpression::Value(value)))
                                .ok_or_else(|| {
                                    format!(
                                        "the literal `{text}` is not a value of field type `{}` of `{variant}`",
                                        crate::surface::printing::machine_integer_type_name(ty)
                                    )
                                })
                        }
                        AlgebraicValueType::Program(interface_type)
                        | AlgebraicValueType::ObjectPointer(interface_type, _) => {
                            // Validation admits only an argument whose type
                            // converts to the field's exactly, so an integer
                            // argument of another type is widened, as a pure
                            // call's argument is. One of the field's own type
                            // is left as it is, so a constructor rebuilt from
                            // its fields is the value it was built from.
                            let widens = crate::kernel::MachineIntegerType::from_program_type(*interface_type)
                                .is_some()
                                && self
                                    .infer_unconstrained_call_argument_type(argument, environment)?
                                    .and_then(|actual| actual.interface_type())
                                    .is_some_and(|actual| actual.to_kernel_type() != *interface_type);
                            let value =
                                self.lower_contract_expression_to_spec(argument, environment)?;
                            Ok(SpecAlgebraicValue::Program(if *interface_type == ProgramType::VoidPointer {
                                SpecExpression::PointerCoercion(Box::new(value), *interface_type)
                            } else if widens {
                                SpecExpression::Cast(Box::new(value), *interface_type)
                            } else {
                                value
                            }))
                        }
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
                            SpecAlgebraicValue::Program(field) => {
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
                            AlgebraicValueType::Program(value_type)
                            | AlgebraicValueType::ObjectPointer(value_type, _) => {
                                bind_match_program_value(
                                    &mut body_environment,
                                    binding,
                                    *value_type,
                                );
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
                                            binding.kernel_name(),
                                        ),
                                    },
                                );
                            }
                            AlgebraicValueType::Integer => {
                                body_environment.values.remove(binding);
                                body_environment.algebraic_values.remove(binding);
                                let variable = allocate_quantifier_variable(
                                    &mut self.next_quantifier_variable,
                                )?;
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
                        bindings: arm
                            .bindings
                            .iter()
                            .map(SurfaceBinder::kernel_name)
                            .collect(),
                        binding_types: variant.fields.clone(),
                        binding_variables: arm
                            .bindings
                            .iter()
                            .zip(&variant.fields)
                            .map(|(binding, ty)| {
                                if ty == &AlgebraicValueType::Integer {
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
                Ok(SpecAlgebraicExpression {
                    algebraic_type: result_type
                        .ok_or_else(|| "an algebraic match must have an arm".to_string())?,
                    node: SpecAlgebraicExpressionNode::Match {
                        scrutinee: Box::new(scrutinee),
                        arms: lowered_arms,
                    },
                })
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition =
                    self.click_proposition_to_spec_proposition(condition, environment)?;
                let then_branch =
                    self.lower_contract_algebraic_to_spec(then_branch, environment)?;
                let else_branch =
                    self.lower_contract_algebraic_to_spec(else_branch, environment)?;
                if then_branch.algebraic_type != else_branch.algebraic_type {
                    return Err("an algebraic `if` has branches of two types".to_string());
                }
                Ok(SpecAlgebraicExpression {
                    algebraic_type: then_branch.algebraic_type.clone(),
                    node: SpecAlgebraicExpressionNode::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                    },
                })
            }
            ContractExpression::Old(inner) => {
                let old_environment =
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                self.lower_contract_algebraic_to_spec(inner, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                let retained_state = self.point_environment(selector, environment)?.ok_or_else(|| {
                    "algebraic values at unresolved program points are not supported in this slice"
                        .to_string()
                })?;
                self.lower_contract_algebraic_to_spec(expression, &retained_state)
            }
            ContractExpression::Let {
                name,
                click_type,
                value,
                body,
            } => {
                let mut body_environment = environment.clone();
                body_environment.values.remove(name);
                body_environment.integer_values.remove(name);
                body_environment.algebraic_values.remove(name);
                body_environment.array_refs.remove(name);
                if *click_type == Some(ClickType::Integer)
                    || (click_type.is_none()
                        && self.contract_expression_is_integer(value, environment))
                {
                    let value = self.lower_contract_integer_to_spec(value, environment)?;
                    body_environment.integer_values.insert(name.clone(), value);
                } else if matches!(click_type, Some(ClickType::Algebraic(_)))
                    || contract_expression_is_algebraic(
                        value,
                        self.spec_definitions.functions,
                        environment,
                        &mut Vec::new(),
                    )
                {
                    let value = self.lower_contract_algebraic_to_spec(value, environment)?;
                    body_environment
                        .algebraic_values
                        .insert(name.clone(), value);
                } else {
                    let mut value = self.lower_contract_expression_to_spec(value, environment)?;
                    if let Some(ClickType::Program(ty)) = click_type {
                        value = value.at_machine_type(ty.to_kernel_type());
                    }
                    body_environment.values.insert(name.clone(), value);
                }
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
            // A region result that is no enum value: say why, as a call the
            // function does not make.
            ContractExpression::RegionResult(region) => {
                let retained_states = self
                    .retained_states
                    .ok_or("`.result` names a region of a function body being executed")?;
                retained_states
                    .region_result_value_at(region, environment.call_result_point.as_ref())?;
                Err(format!(
                    "`{}.result` is not an algebraic value",
                    diagnostics::describe_code_region_ref(region)
                ))
            }
            _ => Err("expected an algebraic value".to_string()),
        }
    }

    fn symbolic_algebraic_variable(
        &mut self,
        name: &SurfaceBinder,
        algebraic_type: &AlgebraicTypeApplication,
        binder_index: usize,
    ) -> Result<SpecAlgebraicExpression, String> {
        if let Some(value) = self.algebraic_variables.get(name) {
            return Ok(value.clone());
        }
        let binder = algebraic_binder_variable(binder_index)?;
        let value = SpecAlgebraicExpression {
            algebraic_type: self.cached_algebraic_kernel_type(algebraic_type)?,
            node: SpecAlgebraicExpressionNode::Variable(binder),
        };
        self.algebraic_variables.insert(name, value.clone());
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
        let algebraic_type = algebraic_kernel_type(self.spec_definitions.functions, application)?;
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
            algebraic_kernel_type_from_parts(self.spec_definitions.functions, name, arguments)?;
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
            .spec_definitions
            .functions
            .get(name)
            .ok_or_else(|| format!("unknown function `{name}`"))?
            .clone();
        let definition =
            self.instantiate_click_function_for_call(&definition, arguments, environment)?;
        if let Some(body) = lambdas::specialize_call(&definition, arguments)? {
            return self.lower_contract_algebraic_to_spec(&body, environment);
        }
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
            .spec_definitions
            .functions
            .is_memory_independent(definition.name());
        definition
            .parameters()
            .iter()
            .zip(arguments)
            .map(|(parameter, argument)| {
                let lowered = match parameter.click_type() {
                    ClickType::Proposition | ClickType::Function { .. } => {
                        Err("specification function parameters are not supported yet".into())
                    }
                    ClickType::Resource => {
                        Err("Resource function parameters are not supported".into())
                    }
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
                    ClickType::Program(interface_type)
                    | ClickType::CObjectPointer { interface_type, .. }
                        if crate::surface::lowering::argument_is_null_pointer_constant(
                            argument,
                            *interface_type,
                        ) =>
                    {
                        let pointer = SpecExpression::Value(ProgramValue::typed_pointer(
                            crate::kernel::Address::null(),
                            interface_type.to_kernel_type(),
                        ));
                        Ok(match click_array_element_type(*interface_type) {
                            Some(element_type) => {
                                crate::kernel::SpecPureFunctionArgument::ArrayRef {
                                    point: if memory_independent {
                                        crate::kernel::SpecPoint::At(
                                            crate::kernel::ProgramPoint::of_memory(
                                                &crate::kernel::value_independent_click_memory(),
                                            ),
                                        )
                                    } else {
                                        environment.current_point.clone()
                                    },
                                    pointer,
                                    element_type,
                                }
                            }
                            None => crate::kernel::SpecPureFunctionArgument::Value(pointer),
                        })
                    }
                    ClickType::Program(_) | ClickType::CObjectPointer { .. }
                        if parameter_is_click_array_ref(parameter) =>
                    {
                        let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                        Ok(crate::kernel::SpecPureFunctionArgument::ArrayRef {
                            // A function that reads no memory is a function of
                            // its argument values, so its pointer arguments are
                            // anchored to one canonical state instead of the
                            // ambient one. Without this the same proposition is a
                            // different term on either side of a C write, and a
                            // `fold` cannot discharge a body fact that applies a
                            // pure predicate to a pointer (gap 42).
                            point: if memory_independent {
                                crate::kernel::SpecPoint::At(
                                    crate::kernel::ProgramPoint::of_memory(
                                        &crate::kernel::value_independent_click_memory(),
                                    ),
                                )
                            } else {
                                array_ref.point
                            },
                            pointer: array_ref.pointer,
                            element_type: array_ref.element_type,
                        })
                    }
                    ClickType::Program(interface_type) => {
                        // An argument is at its parameter's type (G2).
                        let value = self
                            .lower_pure_parameter_argument_to_spec(
                                parameter,
                                argument,
                                environment,
                            )?
                            .at_machine_type(interface_type.to_kernel_type());
                        Ok(crate::kernel::SpecPureFunctionArgument::Value(value))
                    }
                    ClickType::CObjectPointer { .. } => {
                        let value = self.lower_pure_parameter_argument_to_spec(
                            parameter,
                            argument,
                            environment,
                        )?;
                        Ok(crate::kernel::SpecPureFunctionArgument::Value(value))
                    }
                }?;
                Ok(match parameter.pointer_object_class() {
                    Some(object_class) => crate::kernel::SpecPureFunctionArgument::ObjectPointer {
                        argument: Box::new(lowered),
                        object_class,
                    },
                    None => lowered,
                })
            })
            .collect()
    }

    /// Whether `expression` calls a generic function whose result type, a
    /// type parameter, is algebraic at this call: `vec::get(v, i)` with `v`
    /// a `Vec<T>` of a theorem's rigid `T`.
    fn generic_call_returns_algebraic(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> bool {
        let ContractExpression::Call { name, arguments } = expression else {
            return false;
        };
        let Some(definition) = self.spec_definitions.functions.get(name).cloned() else {
            return false;
        };
        if !matches!(definition.return_type(), ClickType::Parameter(_)) {
            return false;
        }
        self.instantiate_click_function_for_call(&definition, arguments, environment)
            .is_ok_and(|instance| matches!(instance.return_type(), ClickType::Algebraic(_)))
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
            ClickType::Resource => Ok(Some(ClickType::Resource)),
            ClickType::Function { .. } => self
                .contract_expression_click_type_in_scope(argument, environment, &mut Vec::new())
                .map(Some)
                .ok_or_else(|| "callback argument needs a concrete lambda".into()),
            ClickType::Proposition => Err("proposition parameters are not supported yet".into()),
            ClickType::Algebraic(_) => {
                let value = self.lower_contract_algebraic_to_spec(argument, environment)?;
                Ok(Some(generics::click_type_from_algebraic_value_type(
                    &value.algebraic_type.value_type(),
                )))
            }
            // A `T*` parameter binds `T` from the argument's pointer type,
            // as a `T` parameter binds it from the argument's type.
            ClickType::Program(InterfaceType::ParameterPointer(_)) | ClickType::Parameter(_) => {
                self.infer_unconstrained_call_argument_type(argument, environment)
            }
            ClickType::Program(_) | ClickType::CObjectPointer { .. } => Ok(Some(expected.clone())),
            ClickType::Integer => Ok(Some(ClickType::Integer)),
        }
    }

    fn infer_unconstrained_call_argument_type(
        &mut self,
        argument: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<Option<ClickType>, String> {
        if let Some(cast_type) = generics::explicit_cast_click_type(argument) {
            return Ok(Some(cast_type));
        }
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
            ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
                Ok(Some(generics::click_type_from_program_value(value)))
            }
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => {
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
            ContractExpression::Call { name, arguments } => {
                let definition = self
                    .spec_definitions
                    .functions
                    .get(name)
                    .ok_or_else(|| format!("unknown function `{name}`"))?
                    .clone();
                let definition =
                    self.instantiate_click_function_for_call(&definition, arguments, environment)?;
                Ok(Some(definition.return_type().clone()))
            }
            // Pointer arithmetic keeps its pointer's type: `bytes + k` is a
            // `*const u8` as `bytes` is.
            ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) => {
                let left = self.infer_unconstrained_call_argument_type(left, environment)?;
                if left
                    .as_ref()
                    .is_some_and(|ty| ty.interface_type().is_some_and(|c| c.is_pointer()))
                {
                    return Ok(left);
                }
                if matches!(argument, ContractExpression::Add(..)) {
                    let right = self.infer_unconstrained_call_argument_type(right, environment)?;
                    if right
                        .as_ref()
                        .is_some_and(|ty| ty.interface_type().is_some_and(|c| c.is_pointer()))
                    {
                        return Ok(right);
                    }
                }
                Ok(None)
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
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                self.lower_contract_sequence_to_spec(inner, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                if let Some(retained_state) = self.point_environment(selector, environment)? {
                    return self.lower_contract_sequence_to_spec(expression, &retained_state);
                }
                match self.resolve_visit_selector(selector, environment)? {
                    ResolvedProgramPoint::Current => {
                        self.lower_contract_sequence_to_spec(expression, environment)
                    }
                    ResolvedProgramPoint::FunctionEntry => {
                        let old_environment = environment
                            .old_state(&self.entry_values, &self.entry_state.program_point())?;
                        self.lower_contract_sequence_to_spec(expression, &old_environment)
                    }
                    ResolvedProgramPoint::LoopEntry(_) => Err(
                        "sequence states at loop entry are not in the first sequence slice"
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
                environment.old_state(&self.entry_values, &self.entry_state.program_point())
            }
        }
    }

    fn contract_segment_element_width(
        &self,
        segment: &ContractSegment,
        environment: &SpecElaborationContext,
    ) -> Result<u32, String> {
        // Whole-object bounds were prepared in four-byte coordinates, as
        // in resource_lowering::contract_segment_element_width_for_result_type.
        // Instantiating a typed declaration must not reinterpret those bounds
        // using the caller's byte-array backing or pointer value type.
        if matches!(
            segment.surface,
            ContractSegmentSurface::Object(_) | ContractSegmentSurface::ObjectPlace { .. }
        ) {
            return Ok(4);
        }
        if let Some(width) = segment.field_element_width() {
            return Ok(width);
        }
        // Whole-object and field syntax has already lowered its storage
        // size to the carrier's coordinates. Only an element range still
        // needs the instantiated generic pointee's physical stride.
        if !matches!(segment.surface, ContractSegmentSurface::Range { .. }) {
            return Ok(self
                .program_expression_array_element_type(&segment.base, environment)
                .unwrap_or(ProgramType::Int32)
                .byte_width());
        }
        if let ProgramExpression::Variable(name) = &segment.base
            && let Some(width) = name.metadata_in(&self.parameter_pointer_element_widths)
        {
            return Ok(*width);
        }
        // A generic range retains the nominal pointer value at instantiation.
        // Its scalar carrier is not the aggregate's physical stride.
        if let Some(pointer) = self.direct_pointer_value(&segment.base, environment) {
            return self.spec_definitions.pointer_element_width(pointer);
        }
        Ok(self
            .program_expression_array_element_width(&segment.base, environment)
            .unwrap_or_else(|| {
                self.program_expression_array_element_type(&segment.base, environment)
                    .unwrap_or(ProgramType::Int32)
                    .byte_width()
            }))
    }

    fn direct_pointer_value<'b>(
        &'b self,
        expression: &'b ProgramExpression,
        environment: &'b SpecElaborationContext,
    ) -> Option<&'b crate::kernel::Pointer> {
        if let ProgramExpression::Variable(name) = expression
            && name.local_id().is_some()
            && let Some(state) = environment.reference_state.as_ref()
        {
            return state.locals().get(name)?.pointer();
        }
        match expression {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => Some(pointer),
            ProgramExpression::Variable(name) => match name.named_in(&environment.values) {
                Some(SpecExpression::Value(ProgramValue::Pointer(pointer))) => Some(pointer),
                _ => None,
            },
            _ => None,
        }
    }

    fn lower_contract_segment_base_to_spec(
        &self,
        expression: &ProgramExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        self.lower_program_expression_to_spec(expression, environment)
    }

    #[inline(never)]
    fn lower_at_resource_subject_to_spec(
        &mut self,
        selector: &ProgramPointSelector,
        resource: &ResourceSubject,
        environment: &SpecElaborationContext,
    ) -> Result<SpecResource, String> {
        // Naming a saved instance only needs the existing snapshot/identity
        // lookup; do not construct a value environment for unrelated locals.
        if let ResourceSubject::Instance { name, identity, .. } = resource
            && let Some(state) = self.retained_states.and_then(|states| states.get(selector))
        {
            let instance = state
                .resource_instance_at_path(*identity, &[])
                .ok_or_else(|| format!("resource instance `{name}` is not owned at this state"))?;
            return Ok(SpecResource::Value(Resource::Instance(instance.clone())));
        }
        if let Some(snapshot) = self.point_environment(selector, environment)? {
            return self.lower_resource_subject_to_spec(resource, &snapshot);
        }
        match self.resolve_visit_selector(selector, environment)? {
            ResolvedProgramPoint::Current => {
                self.lower_resource_subject_to_spec(resource, environment)
            }
            ResolvedProgramPoint::FunctionEntry => {
                let old =
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                self.lower_resource_subject_to_spec(resource, &old)
            }
            _ => Err("`at(...)` resources require a recorded state".into()),
        }
    }

    fn lower_resource_subject_to_spec(
        &mut self,
        resource: &ResourceSubject,
        environment: &SpecElaborationContext,
    ) -> Result<SpecResource, String> {
        match resource {
            ResourceSubject::At { selector, resource } => {
                self.lower_at_resource_subject_to_spec(selector, resource, environment)
            }
            ResourceSubject::Emp => Ok(SpecResource::Value(Resource::Emp)),
            ResourceSubject::Star(left, right) => Ok(SpecResource::Star(
                Box::new(self.lower_resource_subject_to_spec(left, environment)?),
                Box::new(self.lower_resource_subject_to_spec(right, environment)?),
            )),
            ResourceSubject::Instance { identity, name, at } => {
                // `at(point, name)` reads the named state; inside an
                // enclosing state a bare name reads that state.
                let named = match at {
                    Some(selector) => Some(
                        self.retained_states
                            .and_then(|retained_states| retained_states.get(selector))
                            .ok_or_else(|| {
                                format!("`at(..., {name})` names a state that is not recorded here")
                            })?,
                    ),
                    None => None,
                };
                if let Some(state) = named.or(environment.reference_state.as_ref()) {
                    let instance =
                        state
                            .resource_instance_at_path(*identity, &[])
                            .ok_or_else(|| {
                                format!("resource instance `{name}` is not owned at this state")
                            })?;
                    Ok(SpecResource::Value(Resource::Instance(instance.clone())))
                } else {
                    Ok(SpecResource::Instance {
                        identity: *identity,
                        at_entry: environment.at_function_entry,
                    })
                }
            }
            ResourceSubject::Footprint(region) => Ok(SpecResource::Value(
                self.retained_states
                    .ok_or("region footprint requires execution states")?
                    .footprint(region)?,
            )),
            ResourceSubject::Parameter { index, .. } => Ok(SpecResource::Value(
                crate::kernel::Resource::Parameter(crate::kernel::Variable(*index as u64)),
            )),
            ResourceSubject::Captured { value, .. } => Ok(SpecResource::Value(value.clone())),

            ResourceSubject::SavedMemory { base, start, end } => {
                let declared_width = self.contract_pointer_element_width(base, environment);
                let base = self.lower_contract_expression_to_spec(base, environment)?;
                // Recorded aggregate parameter reads carry their declared field
                // type in the lowered load, rather than in the parser's C
                // fragment. These unsigned pointer carriers are unambiguous;
                // nominal record pointers use a different carrier and still
                // require their physical layout metadata above.
                let element_width = declared_width
                    .or(match &base {
                        SpecExpression::MemoryLoad { value_type, .. }
                        | SpecExpression::AggregateFieldValue { value_type, .. } => {
                            match value_type {
                                ProgramType::UInt8Pointer => Some(1),
                                ProgramType::UInt32Pointer => Some(4),
                                _ => None,
                            }
                        }
                        _ => None,
                    })
                    .ok_or("saved memory base must be a pointer with a known element width")?;
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                Ok(match end {
                    Some(end) => SpecResource::Memory {
                        base,
                        start,
                        end: self.lower_contract_expression_to_spec(end, environment)?,
                        element_width,
                    },
                    None => SpecResource::Memory {
                        base: SpecExpression::PointerOffset {
                            pointer: Box::new(base),
                            elements: Box::new(start),
                            byte_width: element_width,
                        },
                        start: SpecExpression::Value(int32(0)),
                        end: SpecExpression::Value(int32(1)),
                        element_width,
                    },
                })
            }
            ResourceSubject::Memory(segment) => {
                let environment = self.spec_segment_environment(segment, environment)?;
                Ok(SpecResource::Memory {
                    base: self.lower_contract_segment_base_to_spec(&segment.base, &environment)?,
                    start: self.lower_program_expression_to_spec(&segment.start, &environment)?,
                    end: self.lower_program_expression_to_spec(&segment.end, &environment)?,
                    element_width: self.contract_segment_element_width(segment, &environment)?,
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
    fn point_environment(
        &self,
        selector: &ProgramPointSelector,
        environment: &SpecElaborationContext,
    ) -> Result<Option<SpecElaborationContext>, String> {
        let Some(state) = self
            .retained_states
            .and_then(|retained_states| retained_states.get(selector))
        else {
            return Ok(None);
        };
        let mut values = environment.values.clone();
        // A parameter reads as its entry value at any state that does not
        // bind it as a local, which is every state taken before its first
        // statement. The context's own binding is the current value, and a
        // mark taken before a reassignment used to read the value after it.
        values.extend(
            self.entry_values
                .iter()
                .map(|(name, value)| (name.clone(), SpecExpression::Value(value.clone()))),
        );
        if let Some(names) = &self.capture_referenced_names {
            for name in names {
                check_integer_lowering_work(1)?;
                if let Some(value) = state
                    .locals()
                    .get(name)
                    .map(|value| value.clone().into_native())
                    .or_else(|| state.held_local_value(name))
                    .or_else(|| {
                        // Aggregates are address-backed places, not entries in
                        // object_values. A recorded private parameter must
                        // override the caller-image entry binding even after
                        // the live parameter has left scope.
                        let layout = state.locals().aggregate_layout(name)?;
                        if matches!(layout.value_type(), Some(ProgramType::Parameter(_))) {
                            return None;
                        }
                        Some(ProgramValue::typed_pointer(
                            state.locals().aggregate_object_pointer(name)?.clone(),
                            ProgramType::UInt8Pointer,
                        ))
                    })
                {
                    values.insert(name.clone(), SpecExpression::Value(value));
                }
            }
        } else {
            values.extend(state.locals().object_values().filter_map(|(name, value)| {
                Some((
                    state.locals().active_source_name(name)?.to_owned(),
                    SpecExpression::Value(value.clone().into_native()),
                ))
            }));
            // A local that keeps its value in memory is named by the read of
            // its object in the state's memory.
            values.extend(
                state
                    .locals()
                    .held_value_locals()
                    .filter_map(|(name, _, _)| {
                        Some((
                            state.locals().active_source_name(name)?.to_owned(),
                            SpecExpression::Value(state.held_local_value(name)?),
                        ))
                    }),
            );
        }
        let mut array_refs = environment
            .array_refs
            .iter()
            .map(|(name, array_ref)| {
                (
                    name.clone(),
                    SpecArrayRef {
                        point: SpecPoint::At(state.program_point()),
                        pointer: array_ref.pointer.clone(),
                        element_type: array_ref.element_type,
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        if let Some(names) = &self.capture_referenced_names {
            for name in names {
                check_integer_lowering_work(1)?;
                if let Some((value, element_type)) = state.locals().array_object_value(name) {
                    array_refs.insert(
                        name.clone().into(),
                        SpecArrayRef {
                            point: SpecPoint::At(state.program_point()),
                            pointer: SpecExpression::Value(value),
                            element_type,
                        },
                    );
                }
            }
        } else {
            array_refs.extend(state.locals().array_object_values().filter_map(
                |(name, value, element_type)| {
                    Some((
                        SurfaceBinder::from(state.locals().active_source_name(name)?),
                        SpecArrayRef {
                            point: SpecPoint::At(state.program_point()),
                            pointer: SpecExpression::Value(value),
                            element_type,
                        },
                    ))
                },
            ));
        }
        Ok(Some(SpecElaborationContext {
            values,
            integer_values: environment.integer_values.clone(),
            algebraic_values: environment.algebraic_values.clone(),
            array_refs: array_refs.into_iter().collect(),
            // The state's own memory is the memory here; an outer
            // binding's state does not reach into it.
            array_points: PersistentBinderMap::default(),
            current_point: SpecPoint::At(state.program_point()),
            current_loop_entry: None,
            function_contract: false,
            at_function_entry: false,
            reference_state: Some(state.clone()),
            call_result_point: Some(selector.clone()),
            contract_result_in_scope: environment.contract_result_in_scope,
            contract_result: environment.contract_result.clone(),
            checking_definedness: environment.checking_definedness,
        }))
    }

    /// Read a scalar field of an aggregate result at its producer's exit.
    fn lower_region_result_read(
        &mut self,
        region: &CodeRegionRef,
        accesses: &[RegionParameterAccess<'_>],
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let retained_states = self
            .retained_states
            .ok_or("aggregate result requires a function execution")?;
        let index = retained_states.result_region_index(region)?;
        let layout = retained_states
            .source_layout
            .as_ref()
            .ok_or("aggregate result requires a source layout")?;
        let mut path = String::new();
        for access in accesses {
            match access {
                RegionParameterAccess::Field(name) => {
                    if !path.is_empty() {
                        path.push('.');
                    }
                    path.push_str(name);
                }
                RegionParameterAccess::Index(index) => {
                    let i = literal_element_index(index)
                        .ok_or("aggregate result array fields require a literal index")?;
                    path.push_str(&format!("[{i}]"));
                }
            }
        }
        let (field, element) = match layout.aggregate_result_field(index, &path) {
            Some(field) => (field, None),
            None => {
                let Some((last, _)) = accesses.split_last() else {
                    unreachable!()
                };
                let RegionParameterAccess::Index(position) = last else {
                    return Err(format!(
                        "`{}.result` has no aggregate field `{path}`",
                        diagnostics::describe_code_region_ref(region)
                    ));
                };
                let position = literal_element_index(position)
                    .ok_or("aggregate result array fields require a literal index")?;
                let cut = path.rfind('[').expect("indexed path");
                let field = layout
                    .aggregate_result_field(index, &path[..cut])
                    .ok_or_else(|| format!("aggregate result has no field `{}`", &path[..cut]))?;
                (field, Some(position))
            }
        };
        let (offset, value_type) = match element {
            Some(position) => {
                let (element, count) =
                    super::resource_lowering::array_field_elements(field.program_type())
                        .ok_or("result field is not an array")?;
                if position >= count {
                    return Err(format!("result array field has {count} elements"));
                }
                (
                    field.offset_bytes() + position * element.byte_width(),
                    element,
                )
            }
            None => (field.offset_bytes(), field.program_type()),
        };
        if super::resource_lowering::array_field_elements(value_type).is_some() {
            return Err("read an element of the aggregate result array field".into());
        }
        let pointer = retained_states.region_result_value(region)?;
        let read = ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
            pointer: Box::new(crate::kernel::program_expression::pointer_offset_bytes(
                ProgramExpression::Value(pointer),
                offset,
            )),
            value_type,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        });
        self.lower_at_expression_to_spec(
            &ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Region(index),
                kind: ProgramPointKind::Exit,
            }),
            &read,
            environment,
        )
    }

    /// `R.parameter(name).field[i]`: the scalar the call at `R` read from
    /// its copy of an aggregate argument. The copy's layout is the one the
    /// call bound, recorded at `R`'s parameter point, so the read is the
    /// typed load at that field (and element) of the copy, at that point.
    fn lower_region_parameter_read(
        &mut self,
        region: &CodeRegionRef,
        name: &str,
        accesses: &[RegionParameterAccess<'_>],
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let spelled = || {
            format!(
                "{}.parameter({name})",
                diagnostics::describe_code_region_ref(region)
            )
        };
        let retained_states = self.retained_states.ok_or_else(|| {
            format!(
                "`{}` names a call of a function body being executed",
                spelled()
            )
        })?;
        let index = retained_states
            .result_region_index(region)
            .map_err(|error| format!("`{}`: {error}", spelled()))?;
        let point = ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Parameters,
        };
        let bound = retained_states.get(&point).ok_or_else(|| {
            format!(
                "`{}` names a by-value aggregate argument of a call, and no call at `{}` has been prepared or stepped with one",
                spelled(),
                diagnostics::describe_code_region_ref(region)
            )
        })?;
        let layout = bound.locals().aggregate_layout(name).ok_or_else(|| {
            format!(
                "the call at `{}` has no by-value aggregate parameter `{name}`",
                diagnostics::describe_code_region_ref(region)
            )
        })?;
        let field_count = accesses
            .iter()
            .take_while(|access| matches!(access, RegionParameterAccess::Field(_)))
            .count();
        if field_count == 0 {
            return Err(format!("read a field of `{}`", spelled()));
        }
        // Aggregate layouts flatten embedded records into dotted field paths.
        // Keep that exact path when reading a copied parameter, just as a
        // returned aggregate field does; a span's size is such a nested field.
        let field_name = accesses[..field_count]
            .iter()
            .map(|access| match access {
                RegionParameterAccess::Field(name) => *name,
                _ => unreachable!(),
            })
            .collect::<Vec<_>>()
            .join(".");
        let rest = &accesses[field_count..];
        let field = layout
            .fields()
            .iter()
            .find(|field| {
                field.name() == field_name
                    || field.name().strip_prefix('_') == Some(field_name.as_str())
            })
            .ok_or_else(|| format!("`{}` has no field `{field_name}`", spelled()))?;
        let (offset, value_type) = match rest {
            [] => (field.offset_bytes(), field.program_type()),
            [RegionParameterAccess::Index(index)] => {
                let (element, length) =
                    super::resource_lowering::array_field_elements(field.program_type())
                        .ok_or_else(|| format!("`{}.{field_name}` is not an array", spelled()))?;
                let position = literal_element_index(index).ok_or_else(|| {
                    format!(
                        "an element of `{}.{field_name}` is selected by a literal index",
                        spelled()
                    )
                })?;
                if position >= length {
                    return Err(format!(
                        "`{}.{field_name}` has {length} elements",
                        spelled()
                    ));
                }
                (
                    field.offset_bytes() + position * element.byte_width(),
                    element,
                )
            }
            _ => {
                return Err(format!(
                    "`{}` is read one field, or one element of an array field, at a time",
                    spelled()
                ));
            }
        };
        if super::resource_lowering::array_field_elements(value_type).is_some() {
            return Err(format!("read an element of `{}.{field_name}`", spelled()));
        }
        let read = ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
            pointer: Box::new(crate::kernel::program_expression::pointer_offset_bytes(
                ProgramExpression::Variable(name.into()),
                offset,
            )),
            value_type,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        });
        self.lower_at_expression_to_spec(
            &ProgramPointSelector::ProgramPoint(point),
            &read,
            environment,
        )
    }

    fn lower_at_expression_to_spec(
        &mut self,
        selector: &ProgramPointSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        if let Some(retained_state) = self.point_environment(selector, environment)? {
            return self.lower_contract_expression_to_spec(expression, &retained_state);
        }
        if self.retained_states.is_none()
            && let ProgramPointSelector::Mark(name) = selector
            && let Some(loop_index) = environment.current_loop_entry
        {
            return Err(format!(
                "proof-local mark `{name}` cannot be used in a loop invariant; use `at(loop({loop_index}).entry, ...)` for that loop's entry state"
            ));
        }
        match self.resolve_visit_selector(selector, environment)? {
            ResolvedProgramPoint::Current => {
                self.lower_contract_expression_to_spec(expression, environment)
            }
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                Ok(SpecExpression::LoopEntryState(Box::new(
                    self.lower_contract_expression_to_spec(expression, environment)?,
                )))
            }
        }
    }

    fn resolve_visit_selector(
        &self,
        selector: &ProgramPointSelector,
        environment: &SpecElaborationContext,
    ) -> Result<ResolvedProgramPoint, String> {
        match selector {
            ProgramPointSelector::ProgramPoint(program_point)
                if self.branch_join_target == Some(program_point) =>
            {
                Ok(ResolvedProgramPoint::Current)
            }
            ProgramPointSelector::ProgramPoint(program_point) => {
                self.resolve_program_point_ref(program_point, environment)
            }
            ProgramPointSelector::Mark(name) if self.retained_states.is_some() => Err(format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )),
            ProgramPointSelector::Mark(name) => Err(format!(
                "proof-local mark `{name}` is available only in an execution proof"
            )),
        }
    }

    fn resolve_program_point_ref(
        &self,
        program_point: &ProgramPointRef,
        environment: &SpecElaborationContext,
    ) -> Result<ResolvedProgramPoint, String> {
        if let CodeRegionRef::Path(_) = &program_point.region {
            let retained_states = self
                .retained_states
                .ok_or("`statement(i)` regions name points of a function body being executed")?;
            let point = retained_states.source_point(program_point)?;
            return self
                .resolve_program_point_ref(&point, environment)
                .map_err(|error| {
                    format!(
                        "`{}` is `{}`: {error}",
                        crate::surface::diagnostics::describe_program_point_ref(program_point),
                        crate::surface::diagnostics::describe_program_point_ref_as_recorded(&point)
                    )
                });
        }
        let region = self.resolve_code_region_ref(&program_point.region)?;
        match (region, program_point.kind) {
            (CodeRegion::Function | CodeRegion::Loop(_), ProgramPointKind::Parameters) => {
                Err("`.parameter(name)` names a by-value parameter of a call's region".to_string())
            }
            (CodeRegion::Function, ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::FunctionEntry)
            }
            (CodeRegion::Loop(index), ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::LoopEntry(index))
            }
            // `result` is in scope only once the function has returned, in a
            // postcondition or at a returned outcome: the state read there is
            // the exit state. Before the return there is no exit to read.
            (CodeRegion::Function, ProgramPointKind::Exit)
                if environment.contract_result_in_scope =>
            {
                Ok(ResolvedProgramPoint::Current)
            }
            (CodeRegion::Function, ProgramPointKind::Exit) => Err(
                "`at(function.exit, ...)` is available only once the function has returned"
                    .to_string(),
            ),
            (CodeRegion::Loop(_), ProgramPointKind::Exit) | (CodeRegion::Statement(_), _)
                if self.retained_states.is_some() =>
            {
                if let Some(refusal) = self.retained_states.and_then(|retained_states| {
                    retained_states.ambiguous_exit_refusal(&ProgramPointSelector::ProgramPoint(
                        program_point.clone(),
                    ))
                }) {
                    return Err(refusal);
                }
                Err(format!(
                    "no symbolic state was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                    crate::surface::diagnostics::describe_program_point_ref(program_point)
                ))
            }
            (CodeRegion::Loop(index), ProgramPointKind::Exit) => Err(format!(
                "`at(loop({index}).exit, ...)` requires a recorded state in an execution proof"
            )),
            (CodeRegion::Statement(_), _) => Err(format!(
                "`at({}, ...)` is not supported in this context yet",
                crate::surface::diagnostics::describe_program_point_ref(program_point)
            )),
        }
    }

    fn resolve_code_region_ref(&self, region_ref: &CodeRegionRef) -> Result<CodeRegion, String> {
        region_ref
            .resolve(self.structural_clauses)
            .map_err(|error| match error {
                CodeRegionResolutionError::ExecutionTargetOnly(_) => {
                    format!("{error}; use `mark` to name the reached state")
                }
                CodeRegionResolutionError::UnknownLabel(_)
                | CodeRegionResolutionError::StatementRegionTarget => error.to_string(),
            })
    }

    fn lower_program_binding_to_spec(
        &self,
        name: impl Into<crate::kernel::BindingName>,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let name = name.into();
        crate::instrumentation::record_deterministic_work(1);
        if let Some(id) = name.static_id() {
            let metadata = id
                .metadata()
                .ok_or_else(|| format!("unknown C static declaration `{id}`"))?;
            let pointer = crate::kernel::SymbolicMemory::global_pointer(&name);
            if metadata.aggregate || metadata.array_shape.is_some() {
                let pointer_type = if metadata.aggregate {
                    ProgramType::UInt8Pointer
                } else {
                    metadata
                        .program_type
                        .array_element_type()
                        .and_then(ProgramType::pointer_to)
                        .ok_or_else(|| format!("static array `{id}` has no element pointer type"))?
                };
                return Ok(SpecExpression::Value(
                    ProgramValue::typed_pointer_with_pointee_constant(
                        pointer,
                        pointer_type,
                        metadata.constant,
                    ),
                ));
            }
            if metadata.volatile {
                return Err(format!(
                    "volatile object `{id}` cannot be read in a specification"
                ));
            }
            // A typed read names its scalar type separately from the storage
            // address. Use the byte-address carrier also for bools and pointer
            // cells whose C pointer-to-type has no kernel carrier.
            let pointer_type = ProgramType::UInt8Pointer;
            return Ok(SpecExpression::MemoryLoad {
                point: environment.current_point.clone(),
                pointer: Box::new(SpecExpression::Value(
                    ProgramValue::typed_pointer_with_pointee_constant(
                        pointer,
                        pointer_type,
                        metadata.constant,
                    ),
                )),
                value_type: metadata.program_type,
            });
        }

        if name.local_id().is_some()
            && let Some(state) = environment.reference_state.as_ref().or_else(|| {
                (environment.at_function_entry && !environment.function_contract)
                    .then_some(self.entry_state)
            })
            && let Some(value) = state
                .locals()
                .get(&name)
                .map(|value| value.clone().into_native())
                .or_else(|| state.held_local_value(&name))
                .or_else(|| {
                    state
                        .locals()
                        .array_object_value(&name)
                        .map(|(value, _)| value)
                })
        {
            return Ok(SpecExpression::Value(value));
        }
        // Reference carriers are program bindings, outside the lexical binder
        // namespace. Their pointer is fixed when the reference is initialized;
        // old-state reads change the referent's memory, never that pointer.
        if let Some(referent) = name.reference_referent() {
            let state = environment.reference_state.as_ref().or_else(|| {
                if environment.at_function_entry {
                    Some(self.entry_state)
                } else {
                    self.local_type_state
                }
            });
            if let Some(value) = state
                .and_then(|state| state.locals().get(&name))
                .map(|value| value.clone().into_native())
                .or_else(|| {
                    referent
                        .named()
                        .and_then(|name| self.entry_values.get(name))
                        .cloned()
                })
            {
                return Ok(SpecExpression::Value(value));
            }
            if environment.function_contract {
                return Ok(SpecExpression::ProgramExpression(
                    ProgramExpression::Variable(name),
                ));
            }
        }
        if name == crate::kernel::CONTRACT_RESULT
            && let Some(value) = &environment.contract_result
        {
            return Ok(value.as_ref().clone());
        }
        match name.named_in(&environment.values) {
            Some(value) => Ok(value.clone()),
            None if environment
                .reference_state
                .as_ref()
                .is_some_and(|state| state.locals().aggregate_object_pointer(&name).is_some()) =>
            {
                // Automatic aggregates are places rather than ordinary
                // object-value bindings. Resolve only the named place in
                // this recorded state, including after it leaves scope.
                let state = environment
                    .reference_state
                    .as_ref()
                    .expect("checked aggregate state binding");
                let pointer = state
                    .locals()
                    .aggregate_object_pointer(&name)
                    .expect("checked aggregate state binding");
                // An object that holds one value of a library or enum type, a
                // borrowed Rust `Vec` or iterator, is read as that value, as
                // the program reads it.
                if let Some(value_type @ ProgramType::Parameter(parameter)) = state
                    .locals()
                    .aggregate_layout(&name)
                    .and_then(crate::kernel::AggregateLayout::value_type)
                {
                    return Ok(SpecExpression::MemoryLoad {
                        point: environment.current_point.clone(),
                        pointer: Box::new(SpecExpression::Value(ProgramValue::typed_pointer(
                            pointer.clone(),
                            ProgramType::ParameterPointer(parameter),
                        ))),
                        value_type,
                    });
                }
                Ok(SpecExpression::Value(ProgramValue::typed_pointer(
                    pointer.clone(),
                    ProgramType::UInt8Pointer,
                )))
            }
            // An entry read names the aggregate place recorded at entry,
            // including a by-value parameter's private copy. Later automatic
            // locals have no entry binding. Static storage also keeps its
            // place in other fixed-memory contexts.
            None if matches!(environment.current_point, SpecPoint::At(_))
                && self
                    .entry_state
                    .locals()
                    .aggregate_object_pointer(&name)
                    .is_some_and(|pointer| {
                        environment.at_function_entry || pointer.base.is_static_storage_block()
                    }) =>
            {
                let pointer = self
                    .entry_state
                    .locals()
                    .aggregate_object_pointer(&name)
                    .expect("checked storage aggregate binding");
                Ok(SpecExpression::Value(ProgramValue::typed_pointer(
                    pointer.clone(),
                    ProgramType::UInt8Pointer,
                )))
            }
            None if self.entry_state.global_object_type(&name).is_some() => {
                Ok(SpecExpression::MemoryLoad {
                    point: environment.current_point.clone(),
                    pointer: Box::new(SpecExpression::ProgramExpression(
                        ProgramExpression::AddressOf(Box::new(ProgramExpression::Variable(
                            name.clone(),
                        ))),
                    )),
                    value_type: self
                        .entry_state
                        .global_object_type(&name)
                        .expect("checked global object type"),
                })
            }
            None if matches!(environment.current_point, SpecPoint::At(_)) => {
                if name == crate::kernel::CONTRACT_RESULT {
                    Err("`result` is not available inside `old(...)`".to_string())
                } else {
                    Err(format!("unknown old-state variable `{name}`"))
                }
            }
            None => Ok(SpecExpression::ProgramExpression(
                ProgramExpression::Variable(name.clone()),
            )),
        }
    }

    fn lower_program_expression_to_spec(
        &self,
        expression: &ProgramExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        if let ProgramExpression::AddressOf(target)
        | ProgramExpression::CheckedObjectAddress(target) = expression
            && matches!(
                target.as_ref(),
                ProgramExpression::Variable(crate::kernel::BindingName::Generated(_))
            )
        {
            return Err("a specification binder has no C storage address".into());
        }

        if let ProgramExpression::AddressOf(target)
        | ProgramExpression::CheckedObjectAddress(target) = expression
            && let ProgramExpression::Variable(name) = target.as_ref()
            && let Some(id) = name.static_id()
        {
            let metadata = id
                .metadata()
                .ok_or_else(|| format!("unknown C static declaration `{id}`"))?;
            let pointer_type = if metadata.aggregate {
                ProgramType::UInt8Pointer
            } else {
                metadata
                    .program_type
                    .array_element_type()
                    .unwrap_or(metadata.program_type)
                    .pointer_to()
                    .ok_or_else(|| format!("static object `{id}` has no address type"))?
            };
            return Ok(SpecExpression::Value(
                ProgramValue::typed_pointer_with_pointee_constant(
                    crate::kernel::SymbolicMemory::global_pointer(name),
                    pointer_type,
                    metadata.constant,
                ),
            ));
        }
        if !environment.checking_definedness
            && let ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) = expression
            && let ProgramExpression::Index(base, index) = target.as_ref()
            && matches!(
                base.as_ref(),
                ProgramExpression::TypedLoad {
                    value_type: ProgramType::Int32Array(_)
                        | ProgramType::UInt32Array(_)
                        | ProgramType::UInt8Array(_)
                        | ProgramType::Int128Array(_)
                        | ProgramType::Int64Array(_)
                        | ProgramType::UInt128Array(_)
                        | ProgramType::UInt64Array(_),
                    ..
                }
            )
            && let Some(element_type) =
                self.program_expression_array_element_type(base, environment)
            && let Some(pointer_type) = element_type.pointer_to()
        {
            // An inline array decays to its logical address without reading
            // its elements. Preserve that rule when taking an element's address.
            return Ok(SpecExpression::PointerOffset {
                pointer: Box::new(SpecExpression::PointerCoercion(
                    Box::new(self.lower_program_expression_to_spec(base, environment)?),
                    pointer_type,
                )),
                elements: Box::new(self.lower_program_expression_to_spec(index, environment)?),
                byte_width: element_type.byte_width(),
            });
        }
        if !environment.checking_definedness
            && let ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) = expression
            && let ProgramExpression::Index(base, index) = target.as_ref()
            && let Some(byte_width) = self.program_expression_array_element_width(base, environment)
        {
            // Taking an element's address retains its physical stride,
            // including the concrete layout of a generic struct pointee.
            return Ok(SpecExpression::PointerOffset {
                pointer: Box::new(self.lower_program_expression_to_spec(base, environment)?),
                elements: Box::new(self.lower_program_expression_to_spec(index, environment)?),
                byte_width,
            });
        }
        if let ProgramExpression::AddressOf(target)
        | ProgramExpression::CheckedObjectAddress(target) = expression
            && let ProgramExpression::TypedLoad {
                pointer,
                value_type,
                volatile,
                pointee_constant,
                access_class,
                source,
            } = target.as_ref()
        {
            // Evaluate only the base through the selected specification state.
            // Retain the C place steps for provenance, bounds and qualification.
            let mut base = pointer.as_ref();
            let mut steps = Vec::new();
            loop {
                match base {
                    ProgramExpression::Subobject { pointer, width } => {
                        steps.push(crate::kernel::SpecAddressStep::Subobject { width: *width });
                        base = pointer;
                    }
                    ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
                        steps.push(crate::kernel::SpecAddressStep::OffsetBytes { bytes: *bytes });
                        base = pointer;
                    }
                    _ => break,
                }
            }
            return Ok(SpecExpression::ObjectAddress(Box::new(
                crate::kernel::SpecObjectAddress {
                    base: Box::new(self.lower_program_expression_to_spec(base, environment)?),
                    steps,
                    value_type: *value_type,
                    volatile: *volatile,
                    pointee_constant: *pointee_constant,
                    access_class: access_class.clone(),
                    source: source.clone(),
                    checked: matches!(expression, ProgramExpression::CheckedObjectAddress(_)),
                },
            )));
        }
        match expression {
            ProgramExpression::Value(value) => Ok(SpecExpression::Value(value.clone())),
            ProgramExpression::Variable(name) => self.lower_program_binding_to_spec(
                if name.is_named("result") && environment.contract_result_in_scope {
                    crate::kernel::CONTRACT_RESULT
                } else {
                    name.clone()
                },
                environment,
            ),
            ProgramExpression::Subobject { pointer, width } => Ok(SpecExpression::Subobject {
                pointer: Box::new(self.lower_program_expression_to_spec(pointer, environment)?),
                width: *width,
            }),
            ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
                Ok(SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_program_expression_to_spec(pointer, environment)?),
                    elements: Box::new(SpecExpression::Value(int32(*bytes))),
                    byte_width: 1,
                })
            }
            // Arithmetic on a pointer offsets it by whole elements, as C does.
            ProgramExpression::Add(left, right) => {
                if let Some(element_width) =
                    self.program_expression_array_element_width(left, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_program_expression_to_spec(left, environment)?,
                        ),
                        elements: Box::new(
                            self.lower_program_expression_to_spec(right, environment)?,
                        ),
                        byte_width: element_width,
                    });
                }
                if let Some(element_width) =
                    self.program_expression_array_element_width(right, environment)
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_program_expression_to_spec(right, environment)?,
                        ),
                        elements: Box::new(
                            self.lower_program_expression_to_spec(left, environment)?,
                        ),
                        byte_width: element_width,
                    });
                }
                Ok(SpecExpression::Add(
                    Box::new(self.lower_program_expression_to_spec(left, environment)?),
                    Box::new(self.lower_program_expression_to_spec(right, environment)?),
                ))
            }
            ProgramExpression::Subtract(left, right) => {
                if let Some(element_width) =
                    self.program_expression_array_element_width(left, environment)
                    && self
                        .program_expression_array_element_type(right, environment)
                        .is_none()
                {
                    return Ok(SpecExpression::PointerOffset {
                        pointer: Box::new(
                            self.lower_program_expression_to_spec(left, environment)?,
                        ),
                        elements: Box::new(SpecExpression::Subtract(
                            Box::new(SpecExpression::Value(int32(0))),
                            Box::new(self.lower_program_expression_to_spec(right, environment)?),
                        )),
                        byte_width: element_width,
                    });
                }
                Ok(SpecExpression::Subtract(
                    Box::new(self.lower_program_expression_to_spec(left, environment)?),
                    Box::new(self.lower_program_expression_to_spec(right, environment)?),
                ))
            }
            ProgramExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::RustShiftLeft(left, right) => Ok(SpecExpression::RustShiftLeft(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::RustShiftRight(left, right) => Ok(SpecExpression::RustShiftRight(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_program_expression_to_spec(left, environment)?),
                Box::new(self.lower_program_expression_to_spec(right, environment)?),
            )),
            ProgramExpression::Negate(expression) => Ok(SpecExpression::Negate(Box::new(
                self.lower_program_expression_to_spec(expression, environment)?,
            ))),
            ProgramExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_program_expression_to_spec(expression, environment)?,
            ))),
            // Keep scalar operands in the selected environment, including
            // historical range bounds. Raw C evaluation would read live locals
            // under an `at` proposition. Recursive lowering also preserves a
            // byte read's pointee type and a pointer operand's layout width.
            ProgramExpression::Cast {
                expression,
                target_type,
                integer_mode,
                ..
            } if matches!(
                target_type,
                ProgramType::Int32 | ProgramType::UInt32 | ProgramType::Int64
            ) || *target_type == ProgramType::UInt64
                && (!matches!(environment.current_point, SpecPoint::Current)
                        || environment.current_loop_entry.is_some()
                        // A cast introduced by parameter substitution still
                        // reads a quantified value from its lexical environment.
                        || matches!(expression.as_ref(), ProgramExpression::Variable(name)
                            if name.named_in(&environment.values).is_some())
                        || self
                            .program_expression_array_element_width(expression, environment)
                            .is_some())
                || target_type.is_pointer() =>
            {
                let value =
                    Box::new(self.lower_program_expression_to_spec(expression, environment)?);
                Ok(
                    if *integer_mode == crate::kernel::IntegerCastMode::PointerCoercion {
                        SpecExpression::PointerCoercion(value, *target_type)
                    } else {
                        SpecExpression::Cast(value, *target_type)
                    },
                )
            }
            ProgramExpression::Index(base, index) => {
                let element_type = self
                    .program_expression_array_element_type(base, environment)
                    .unwrap_or(ProgramType::Int32);
                let pointer = SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_program_expression_to_spec(base, environment)?),
                    elements: Box::new(self.lower_program_expression_to_spec(index, environment)?),
                    byte_width: element_type.byte_width(),
                };
                Ok(SpecExpression::MemoryLoad {
                    point: environment.current_point.clone(),
                    pointer: Box::new(pointer),
                    value_type: element_type,
                })
            }
            ProgramExpression::TypedLoad {
                pointer,
                value_type:
                    ProgramType::Int32Array(_)
                    | ProgramType::UInt32Array(_)
                    | ProgramType::UInt8Array(_)
                    | ProgramType::Int128Array(_)
                    | ProgramType::Int64Array(_)
                    | ProgramType::UInt128Array(_)
                    | ProgramType::UInt64Array(_),
                ..
            } => self.lower_program_expression_to_spec(pointer, environment),
            ProgramExpression::TypedLoad {
                pointer,
                value_type,
                ..
            } => {
                if matches!(environment.current_point, SpecPoint::Current)
                    && environment.current_loop_entry.is_none()
                    && let Some(parameter) = aggregate_projection_root(pointer)
                    && (parameter
                        .named()
                        .is_some_and(|parameter| self.aggregate_parameters.contains(parameter))
                        || self
                            .entry_state
                            .locals()
                            .aggregate_layout(parameter)
                            .is_some())
                {
                    let mut projection_environment = environment.clone();
                    if let Some(name) = parameter.named() {
                        projection_environment.values.insert(
                            name.to_owned(),
                            SpecExpression::ProgramExpression(ProgramExpression::Variable(
                                parameter.clone(),
                            )),
                        );
                    }
                    return Ok(SpecExpression::AggregateFieldValue {
                        parameter: parameter.clone(),
                        pointer: Box::new(
                            self.lower_program_expression_to_spec(
                                pointer,
                                &projection_environment,
                            )?,
                        ),
                        value_type: *value_type,
                    });
                }
                Ok(SpecExpression::MemoryLoad {
                    point: environment.current_point.clone(),
                    pointer: Box::new(self.lower_program_expression_to_spec(pointer, environment)?),
                    value_type: *value_type,
                })
            }
            ProgramExpression::Load(pointer) => Ok(SpecExpression::MemoryLoad {
                point: environment.current_point.clone(),
                pointer: Box::new(self.lower_program_expression_to_spec(pointer, environment)?),
                value_type: self
                    .program_expression_array_element_type(pointer, environment)
                    .unwrap_or(ProgramType::Int32),
            }),
            expression => {
                let expression = if environment.contract_result_in_scope {
                    substitute_program_expression_in(
                        expression,
                        &ContractSubstitutions::for_contract_result(&BTreeMap::from([(
                            "result".to_string(),
                            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                                crate::kernel::CONTRACT_RESULT,
                            )),
                        )])),
                    )?
                } else {
                    expression.clone()
                };
                Ok(SpecExpression::ProgramExpression(expression))
            }
        }
    }

    fn lower_click_function_call_to_spec(
        &mut self,
        name: &str,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let definition = self
            .spec_definitions
            .functions
            .get(name)
            .ok_or_else(|| format!("unknown function `{name}`"))?
            .clone();
        let definition =
            self.instantiate_click_function_for_call(&definition, arguments, environment)?;
        if let Some(body) = lambdas::specialize_call(&definition, arguments)? {
            return self.lower_contract_expression_to_spec(&body, environment);
        }

        if arguments.len() != definition.parameters().len() {
            return Err(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                arguments.len()
            ));
        }

        let Some(result_type) = definition.return_type().interface_type() else {
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
            pointer_result: self
                .spec_definitions
                .functions
                .pointer_results
                .get(generic_instance_source_name(definition.name()))
                .cloned()
                .flatten(),
            result_object_class: definition.return_object_class().cloned(),
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
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_array_ref_to_spec(selector, expression, environment),
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => {
                if let Some(array_ref) = environment.array_refs.get(name) {
                    return Ok(array_ref.clone());
                }
                Ok(SpecArrayRef {
                    // A binding that names a state of its own reads there.
                    // The pointer is still the name's own, so a physical
                    // pointee width the context carries is preserved.
                    point: environment
                        .array_points
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| environment.current_point.clone()),
                    pointer: self.lower_program_expression_to_spec(
                        &ProgramExpression::Variable((name.clone()).into()),
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
                        point: array_ref.point,
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
                        point: array_ref.point,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    point: environment.current_point.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            ContractExpression::Subtract(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let negative_offset = SpecExpression::Subtract(
                        Box::new(SpecExpression::Value(ProgramValue::Int32(
                            MachineTerm::constant(0),
                        ))),
                        Box::new(offset),
                    );
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        point: array_ref.point,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(negative_offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    point: environment.current_point.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            // A pointer-valued pure call steps by its result's pointee:
            // `slice::as_ptr::<uint8>(s)[1]` reads the byte at offset 1, not
            // the `int32` at offset 4.
            ContractExpression::Call { .. } => {
                let element_type = match self
                    .infer_unconstrained_call_argument_type(expression, environment)?
                    .and_then(|result| result.interface_type())
                    .and_then(|result| result.pointee_type())
                {
                    Some(element_type) => element_type.to_kernel_type(),
                    None => self.contract_array_element_type(expression, environment),
                };
                let pointer = self.lower_contract_expression_to_spec(expression, environment)?;
                Ok(SpecArrayRef {
                    point: environment.current_point.clone(),
                    pointer,
                    element_type,
                })
            }
            _ => Ok(SpecArrayRef {
                point: environment.current_point.clone(),
                pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                element_type: self.contract_array_element_type(expression, environment),
            }),
        }
    }

    fn lower_at_array_ref_to_spec(
        &mut self,
        selector: &ProgramPointSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        if let Some(retained_state) = self.point_environment(selector, environment)? {
            return self.lower_array_ref_to_spec(expression, &retained_state);
        }
        match self.resolve_visit_selector(selector, environment)? {
            ResolvedProgramPoint::Current => self.lower_array_ref_to_spec(expression, environment),
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, &self.entry_state.program_point())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                let SpecArrayRef {
                    point: memory,
                    pointer,
                    element_type,
                } = self.lower_array_ref_to_spec(expression, environment)?;
                let memory = match memory {
                    SpecPoint::Current => SpecPoint::LoopEntry,
                    memory => memory,
                };
                Ok(SpecArrayRef {
                    point: memory,
                    pointer: SpecExpression::LoopEntryState(Box::new(pointer)),
                    element_type,
                })
            }
        }
    }

    fn array_ref_element_type_for_name_in_environment(
        &self,
        name: &str,
        environment: &SpecElaborationContext,
    ) -> ProgramType {
        if name == "result" && environment.contract_result_in_scope {
            return self
                .result_type
                .pointee_type()
                .or_else(|| match environment.contract_result.as_deref() {
                    Some(SpecExpression::Value(ProgramValue::Pointer(pointer))) => {
                        pointer.program_type().pointee_type()
                    }
                    _ => None,
                })
                .unwrap_or(ProgramType::Int32);
        }
        self.declared_pointer_element_type(name)
            .or_else(|| self.entry_state.global_array_element_type(name))
            .or_else(|| {
                environment.values.get(name).and_then(|value| match value {
                    SpecExpression::Value(ProgramValue::Pointer(pointer)) => {
                        pointer.program_type().pointee_type()
                    }
                    _ => None,
                })
            })
            .unwrap_or(ProgramType::Int32)
    }

    fn contract_array_element_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> ProgramType {
        match expression {
            ContractExpression::Let {
                value,
                body,
                name,
                click_type,
            } if matches!(body.as_ref(), ContractExpression::Binding(binding) if binding == name) => {
                click_type
                    .as_ref()
                    .and_then(ClickType::interface_type)
                    .and_then(|ty| ty.to_kernel_type().pointee_type())
                    .unwrap_or_else(|| self.contract_array_element_type(value, environment))
            }
            ContractExpression::ProgramBinding(name) => self
                .declared_pointer_element_type(name)
                .or_else(|| self.entry_state.global_array_element_type(name))
                .or_else(|| {
                    environment.values.get(name).and_then(|value| match value {
                        SpecExpression::Value(ProgramValue::Pointer(pointer)) => {
                            pointer.program_type().pointee_type()
                        }
                        _ => None,
                    })
                })
                .unwrap_or(ProgramType::Int32),
            ContractExpression::CUnary { operand, lowered } => match lowered {
                ProgramExpression::Cast { target_type, .. } => {
                    target_type.pointee_type().unwrap_or(ProgramType::Int32)
                }
                ProgramExpression::PointerOffsetBytes { .. } => {
                    self.contract_array_element_type(operand, environment)
                }
                _ => self
                    .program_expression_array_element_type(lowered, environment)
                    .unwrap_or(ProgramType::Int32),
            },
            ContractExpression::Binding(name)
            | ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::BindingName::Named(name),
            )) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .unwrap_or_else(|| {
                    self.array_ref_element_type_for_name_in_environment(name, environment)
                }),
            // A held resource's arguments are substituted as C values. A
            // pointer value carries its own pointee type, which is the
            // element an index steps by; `uint8*` must not read as `int32*`.
            ContractExpression::ProgramExpression(lowered) => self
                .program_expression_array_element_type(lowered, environment)
                .unwrap_or(ProgramType::Int32),
            ContractExpression::QualifiedC { lowered, .. }
            | ContractExpression::Field { lowered, .. } => self
                .program_expression_array_element_type(lowered, environment)
                .unwrap_or(ProgramType::Int32),
            ContractExpression::At { expression, .. } => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Old(expression) => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Add(left, right) => {
                let left_type = self.contract_array_element_type(left, environment);
                if left_type != ProgramType::Int32 {
                    return left_type;
                }
                self.contract_array_element_type(right, environment)
            }
            ContractExpression::Subtract(left, _) => {
                self.contract_array_element_type(left, environment)
            }
            _ => ProgramType::Int32,
        }
    }

    /// The element width a pure call's result steps by when the call
    /// returns a pointer: its declared result's pointee, at the call's own
    /// type arguments. `None` for any other expression or result.
    fn call_pointer_element_width(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<Option<u32>, String> {
        // A state changes the value read, not the call's declared type.
        if let ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } = expression
        {
            return self.call_pointer_element_width(inner, environment);
        }
        // Only a declared pure function with a pointer result: a built-in
        // conversion such as `to_int32` is not one.
        let ContractExpression::Call { name, .. } = expression else {
            return Ok(None);
        };
        if !self
            .spec_definitions
            .functions
            .get(name)
            .is_some_and(|definition| match definition.return_type() {
                ClickType::Program(interface_type) => {
                    interface_type.is_pointer()
                        || matches!(interface_type, InterfaceType::ParameterPointer(_))
                }
                ClickType::CObjectPointer { .. } => true,
                _ => false,
            })
        {
            return Ok(None);
        }
        Ok(self
            .infer_unconstrained_call_argument_type(expression, environment)?
            .and_then(|result| result.interface_type())
            .and_then(|result| result.pointee_type())
            .map(|element| element.to_kernel_type().byte_width()))
    }

    /// Physical element widths take precedence over scalar resource carriers.
    fn contract_pointer_element_width(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Option<u32> {
        match expression {
            ContractExpression::RegionResult(region) => {
                let ProgramValue::Pointer(pointer) = self
                    .retained_states?
                    .region_result_value_at(region, environment.call_result_point.as_ref())
                    .ok()?
                else {
                    return None;
                };
                self.spec_definitions.pointer_element_width(&pointer).ok()
            }
            ContractExpression::ProgramBinding(name) => self
                .program_expression_array_element_width(
                    &ProgramExpression::Variable((name.clone()).into()),
                    environment,
                ),
            ContractExpression::CUnary { lowered, .. }
            | ContractExpression::QualifiedC { lowered, .. }
            | ContractExpression::ProgramExpression(lowered)
            | ContractExpression::Field { lowered, .. } => {
                self.program_expression_array_element_width(lowered, environment)
            }
            ContractExpression::Old(inner) => {
                self.contract_pointer_element_width(inner, environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => {
                let mut context = environment.clone();
                context.call_result_point = Some(selector.clone());
                self.contract_pointer_element_width(expression, &context)
            }
            ContractExpression::Add(left, right) => self
                .contract_pointer_element_width(left, environment)
                .or_else(|| self.contract_pointer_element_width(right, environment)),
            ContractExpression::Subtract(left, _) => {
                self.contract_pointer_element_width(left, environment)
            }
            _ => self
                .contract_pointer_element_type(expression, environment)
                .map(ProgramType::byte_width),
        }
    }

    /// The element type a contract expression steps by when it is a pointer:
    /// an array reference or a pointer-valued binding in scope, a pointer
    /// fragment, or pointer arithmetic on one. `None` for a scalar.
    fn contract_pointer_element_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Option<ProgramType> {
        match expression {
            ContractExpression::CUnary { operand, lowered } => match lowered {
                ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
                ProgramExpression::PointerOffsetBytes { .. } => {
                    self.contract_pointer_element_type(operand, environment)
                }
                _ => self.program_expression_array_element_type(lowered, environment),
            },
            ContractExpression::ProgramBinding(name) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .or_else(|| {
                    environment.values.get(name).and_then(|value| match value {
                        SpecExpression::Value(ProgramValue::Pointer(pointer)) => {
                            pointer.program_type().pointee_type()
                        }
                        _ => None,
                    })
                }),
            ContractExpression::QualifiedC {
                lowered: expression,
                ..
            }
            | ContractExpression::ProgramExpression(expression)
            | ContractExpression::Field {
                lowered: expression,
                ..
            } => self.program_expression_array_element_type(expression, environment),
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

    fn program_expression_array_element_type(
        &self,
        expression: &ProgramExpression,
        environment: &SpecElaborationContext,
    ) -> Option<ProgramType> {
        if matches!(expression, ProgramExpression::Variable(name) if name.is_named("result"))
            && environment.contract_result_in_scope
        {
            return self.program_expression_array_element_type(
                &ProgramExpression::Variable(crate::kernel::CONTRACT_RESULT),
                environment,
            );
        }
        match expression {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => {
                pointer.program_type().pointee_type()
            }
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) => match target.as_ref() {
                ProgramExpression::TypedLoad { value_type, .. } => Some(*value_type),
                ProgramExpression::Variable(name) => self.c_variable_type(name),
                _ => None,
            },
            ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
            ProgramExpression::Variable(name) => name
                .named_in(&environment.array_refs)
                .map(|array_ref| array_ref.element_type)
                .or_else(|| self.declared_pointer_element_type(name))
                .or_else(|| {
                    (name == &crate::kernel::CONTRACT_RESULT)
                        .then(|| self.result_type.pointee_type())
                        .flatten()
                })
                .or_else(|| self.entry_state.global_array_element_type(name))
                .or_else(|| {
                    name.named_in(&environment.values)
                        .and_then(|value| match value {
                            SpecExpression::Value(ProgramValue::Pointer(pointer)) => {
                                pointer.program_type().pointee_type()
                            }
                            _ => None,
                        })
                }),
            ProgramExpression::TypedLoad { value_type, .. } => match value_type {
                ProgramType::Int32Array(_) => Some(ProgramType::Int32),
                ProgramType::UInt32Array(_) => Some(ProgramType::UInt32),
                ProgramType::Int64Array(_) => Some(ProgramType::Int64),
                ProgramType::Int128Array(_) => Some(ProgramType::Int128),
                ProgramType::UInt64Array(_) => Some(ProgramType::UInt64),
                ProgramType::UInt128Array(_) => Some(ProgramType::UInt128),
                ProgramType::UInt8Array(_) => Some(ProgramType::UInt8),
                value_type => value_type.pointee_type(),
            },
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. } => {
                self.program_expression_array_element_type(pointer, environment)
            }
            ProgramExpression::Add(left, right) => self
                .program_expression_array_element_type(left, environment)
                .or_else(|| self.program_expression_array_element_type(right, environment)),
            ProgramExpression::Subtract(left, _) => {
                self.program_expression_array_element_type(left, environment)
            }
            _ => None,
        }
    }

    /// The physical width used by C pointer arithmetic.  A pointer to a
    /// struct has the nominal compatible `int32*` kernel carrier, so its
    /// pointee layout must be consulted before falling back to `ProgramType`.
    fn program_expression_array_element_width(
        &self,
        expression: &ProgramExpression,
        environment: &SpecElaborationContext,
    ) -> Option<u32> {
        if let ProgramExpression::Variable(name) = expression
            && let Some(width) = name.metadata_in(&self.parameter_pointer_element_widths)
        {
            return Some(*width);
        }
        if let Some(pointer) = self.direct_pointer_value(expression, environment) {
            return self.spec_definitions.pointer_element_width(pointer).ok();
        }
        if matches!(expression, ProgramExpression::Variable(name) if name.is_named("result"))
            && environment.contract_result_in_scope
        {
            return self.program_expression_array_element_width(
                &ProgramExpression::Variable(crate::kernel::CONTRACT_RESULT),
                environment,
            );
        }
        match expression {
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target)
                if matches!(target.as_ref(), ProgramExpression::Index(..)) =>
            {
                let ProgramExpression::Index(base, _) = target.as_ref() else {
                    unreachable!()
                };
                self.program_expression_array_element_width(base, environment)
            }
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) => match target.as_ref() {
                ProgramExpression::TypedLoad { value_type, .. } => Some(value_type.byte_width()),
                ProgramExpression::Variable(name) => {
                    self.c_variable_type(name).map(ProgramType::byte_width)
                }
                _ => None,
            },
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer
                .program_type()
                .pointee_type()
                .map(ProgramType::byte_width),
            ProgramExpression::Cast { target_type, .. } => {
                target_type.pointee_type().map(ProgramType::byte_width)
            }
            ProgramExpression::Variable(name) => name
                .metadata_in(&self.parameter_pointer_element_widths)
                .copied()
                .or_else(|| {
                    name.named_in(&environment.array_refs)
                        .map(|array_ref| array_ref.element_type.byte_width())
                })
                .or_else(|| {
                    self.declared_pointer_element_type(name)
                        .map(|ty| ty.byte_width())
                })
                .or_else(|| {
                    (name == &crate::kernel::CONTRACT_RESULT)
                        .then(|| self.result_type.pointee_type())
                        .flatten()
                        .map(ProgramType::byte_width)
                })
                .or_else(|| {
                    self.entry_state
                        .global_array_element_type(name)
                        .map(ProgramType::byte_width)
                })
                .or_else(|| {
                    name.named_in(&environment.values)
                        .and_then(|value| match value {
                            SpecExpression::Value(ProgramValue::Pointer(pointer)) => pointer
                                .program_type()
                                .pointee_type()
                                .map(ProgramType::byte_width),
                            _ => None,
                        })
                }),
            ProgramExpression::TypedLoad { value_type, .. } => match value_type {
                ProgramType::Int32Array(_) => Some(4),
                ProgramType::Int64Array(_) | ProgramType::UInt64Array(_) => Some(8),
                ProgramType::Int128Array(_) | ProgramType::UInt128Array(_) => Some(16),
                ProgramType::UInt8Array(_) => Some(1),
                value_type => value_type.pointee_type().map(ProgramType::byte_width),
            },
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. } => {
                self.program_expression_array_element_width(pointer, environment)
            }
            ProgramExpression::Add(left, right) => self
                .program_expression_array_element_width(left, environment)
                .or_else(|| self.program_expression_array_element_width(right, environment)),
            ProgramExpression::Subtract(left, _) => {
                self.program_expression_array_element_width(left, environment)
            }
            _ => None,
        }
    }

    fn loop_frame_checks(&self, loop_index: usize) -> Result<Vec<LoopEffectCheck>, ClickError> {
        let mut checks: Vec<LoopEffectCheck> = Vec::new();
        // A loop body can only write memory the function owns, so a loop with
        // no clause of its own inherits the function's owned write footprint
        // instead of becoming an unconditional havoc. An owned footprint that
        // is empty -- a contract that only `views` memory -- is an inherited
        // empty footprint, not the absence of one: the loop still may not
        // write any of the memory it can reach, so every viewed cell is framed
        // across it. The inherited claim stays checked at every back edge, so
        // a body that does write outside the footprint fails there.
        if self.loop_resources.contains_key(&loop_index) {
            // A loop that declares its own resources has the shape of a
            // callee: its footprint is the memory it owns, not everything the
            // function owns. The footprint itself is not lowered here: the
            // kernel derives it from the loop's specs at entry and installs
            // it as the check's validated ranges. The claim stays checked at
            // every back edge.
            checks.push(LoopEffectCheck::new_with_origin(
                LoopEffect::Mutable(Vec::new()),
                LoopEffectSpan::Whole,
                LoopEffectOrigin::DeclaredResource,
                Some(format!("loop {loop_index} declared owned resource frame")),
            ));
        } else if self.inherits_resource_derived_frame
            || !self.implicit_contract_mutable_segments.is_empty()
        {
            checks.push(LoopEffectCheck::new_with_origin(
                LoopEffect::Mutable(self.implicit_contract_mutable_segments.to_vec()),
                LoopEffectSpan::Whole,
                LoopEffectOrigin::InheritedResourceDerived,
                Some(format!("loop {loop_index} inherited owned resource frame")),
            ));
        }
        Ok(checks)
    }
}

/// Only direct object projections qualify. Address-taking, casts and loaded
/// pointers keep ordinary C memory semantics.
fn aggregate_projection_root(
    expression: &ProgramExpression,
) -> Option<&crate::kernel::BindingName> {
    match expression {
        ProgramExpression::Variable(name) => Some(name),
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => aggregate_projection_root(pointer),
        ProgramExpression::Add(pointer, _) | ProgramExpression::Subtract(pointer, _) => {
            aggregate_projection_root(pointer)
        }
        ProgramExpression::TypedLoad {
            pointer,
            value_type:
                ProgramType::Int32Array(_)
                | ProgramType::UInt32Array(_)
                | ProgramType::UInt8Array(_)
                | ProgramType::Int128Array(_)
                | ProgramType::Int64Array(_)
                | ProgramType::UInt128Array(_)
                | ProgramType::UInt64Array(_),
            ..
        } => aggregate_projection_root(pointer),
        _ => None,
    }
}

fn spec_expression_click_type(expression: &SpecExpression) -> Option<ClickType> {
    let program_type = match expression {
        SpecExpression::ResourceField { program_type, .. } => *program_type,
        SpecExpression::Value(value) => {
            return Some(generics::click_type_from_program_value(value));
        }
        SpecExpression::PureFunctionApplication {
            result_type,
            result_object_class: Some(class),
            ..
        } => {
            return Some(ClickType::from_object_pointer_class(
                generics::interface_type_from_program_type(*result_type),
                class,
            ));
        }
        SpecExpression::PureFunctionApplication { result_type, .. }
        | SpecExpression::AggregateFieldValue {
            value_type: result_type,
            ..
        }
        | SpecExpression::MemoryLoad {
            value_type: result_type,
            ..
        } => *result_type,
        SpecExpression::LoopEntryState(inner) => {
            return spec_expression_click_type(inner);
        }
        SpecExpression::If { then_branch, .. } => {
            return spec_expression_click_type(then_branch);
        }
        SpecExpression::Let { body, .. } => {
            return spec_expression_click_type(body);
        }
        SpecExpression::PointerOffset { .. } => ProgramType::VoidPointer,
        SpecExpression::Cast(_, ty) | SpecExpression::PointerCoercion(_, ty) => *ty,
        _ => return None,
    };
    Some(ClickType::Program(
        generics::interface_type_from_program_type(program_type),
    ))
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
        ClickType::Resource => Err("Resource is not an algebraic field type".into()),
        ClickType::Proposition | ClickType::Function { .. } => {
            Err("specification function datatype fields are not supported".into())
        }
        ClickType::Parameter(name) => Err(format!("unresolved type parameter `{name}`")),
        ClickType::Program(interface_type) => {
            Ok(AlgebraicValueType::Program(interface_type.to_kernel_type()))
        }
        ClickType::CObjectPointer { interface_type, .. } => Ok(AlgebraicValueType::ObjectPointer(
            interface_type.to_kernel_type(),
            click_type
                .pointer_object_class()
                .expect("nominal pointer type"),
        )),
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
    if environment
        .algebraic_type_definitions
        .get(name)
        .is_some_and(|definition| definition.is_primitive())
    {
        return Ok(generics::primitive_instance_type(name, arguments));
    }
    let root_type = AlgebraicValueType::Algebraic {
        name: name.to_string(),
        arguments: arguments.to_vec(),
    };
    let mut schemas = BTreeMap::new();
    let mut object_classes = BTreeMap::new();
    collect_algebraic_kernel_schemas(environment, &root_type, &mut schemas, &mut object_classes)?;
    let schemas =
        std::sync::Arc::new(AlgebraicSchemas::new(schemas).with_object_classes(object_classes));
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

/// Collects the schema of `value_type` and of every algebraic type its
/// fields name, with the declared object classes of their pointer fields
/// (`AlgebraicSchemas::with_object_classes`). A type whose fields declare no
/// class records none.
fn collect_algebraic_kernel_schemas(
    environment: &ClickFunctionEnvironment,
    value_type: &AlgebraicValueType,
    schemas: &mut BTreeMap<AlgebraicValueType, std::sync::Arc<[AlgebraicVariantType]>>,
    object_classes: &mut BTreeMap<AlgebraicValueType, crate::kernel::AlgebraicFieldObjectClasses>,
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
    if definition.is_primitive() {
        return Err(format!(
            "the Click library primitive type `{name}` cannot be the type of a datatype's field yet"
        ));
    }
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
    let classes = definition
        .variants()
        .iter()
        .filter_map(|variant| {
            let fields = variant
                .fields()
                .iter()
                .map(|field| match field {
                    AlgebraicFieldType::C { object_class, .. } => object_class.clone(),
                    _ => None,
                })
                .collect::<Vec<_>>();
            fields
                .iter()
                .any(Option::is_some)
                .then(|| (variant.name().to_string(), fields.into()))
        })
        .collect::<crate::kernel::AlgebraicFieldObjectClasses>();
    if !classes.is_empty() {
        object_classes.insert(value_type.clone(), classes);
    }
    for nested in variants
        .iter()
        .flat_map(|variant| variant.fields.iter())
        .filter(|field| matches!(field, AlgebraicValueType::Algebraic { .. }))
    {
        collect_algebraic_kernel_schemas(environment, nested, schemas, object_classes)?;
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
        AlgebraicFieldType::C { interface_type, .. } => Ok(match field.pointer_object_class() {
            Some(class) => {
                AlgebraicValueType::ObjectPointer(interface_type.to_kernel_type(), class)
            }
            None => AlgebraicValueType::Program(interface_type.to_kernel_type()),
        }),
        AlgebraicFieldType::Parameter(name) => definition
            .type_parameters()
            .iter()
            .position(|parameter| parameter == name)
            .and_then(|index| arguments.get(index))
            .cloned()
            .ok_or_else(|| format!("unresolved type parameter `{name}`")),
        AlgebraicFieldType::ParameterPointer(name) => match definition
            .type_parameters()
            .iter()
            .position(|parameter| parameter == name)
            .and_then(|index| arguments.get(index))
        {
            Some(AlgebraicValueType::Program(element)) => {
                crate::surface::generics::interface_type_from_program_type(*element)
                    .pointer_type()
                    .map(|pointer| AlgebraicValueType::Program(pointer.to_kernel_type()))
                    .ok_or_else(|| format!("`{name}*` needs `{name}` to be a C scalar type"))
            }
            Some(AlgebraicValueType::Parameter(parameter)) => Ok(AlgebraicValueType::Program(
                crate::kernel::ProgramType::ParameterPointer(
                    crate::kernel::TypeParameterName::intern(parameter),
                ),
            )),
            Some(_) => Err(format!("`{name}*` needs `{name}` to be a C scalar type")),
            None => Err(format!("unresolved type parameter `{name}`")),
        },
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
    fn captured_integer_freshness_ignores_unrelated_heap_state() {
        use crate::kernel::{
            Address, AddressBase, AddressOffset, MachineTerm, ProgramType, ProgramValue,
            SpecExpression, SpecPoint, SpecPureFunctionArgument, SymbolicMemory,
        };

        let explicit = Variable(2_001);
        let unrelated_heap_variable = Variable(9_000_001);
        let heap_pointer = Address {
            base: AddressBase::Heap(77),
            offset: AddressOffset::Constant(0),
        };
        let memory = SymbolicMemory::new()
            .with_block(heap_pointer.base.clone(), 4)
            .store(
                heap_pointer,
                ProgramValue::Int32(MachineTerm::Variable(unrelated_heap_variable)),
            );
        let captured_array = SpecIntegerExpression::PureFunctionApplication {
            name: "captured_array_value".to_string(),
            arguments: vec![SpecPureFunctionArgument::ArrayRef {
                point: SpecPoint::At(crate::kernel::ProgramPoint::of_memory(&memory)),
                pointer: SpecExpression::Value(ProgramValue::pointer(Address::null())),
                element_type: ProgramType::Int32,
            }],
        };
        let captured_from_machine_load =
            SpecIntegerExpression::FromMachine(Box::new(SpecExpression::MemoryLoad {
                point: SpecPoint::At(crate::kernel::ProgramPoint::of_memory(&memory)),
                pointer: Box::new(SpecExpression::Value(
                    ProgramValue::pointer(Address::null()),
                )),
                value_type: ProgramType::Int32,
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
            "freshness must follow explicit expression identities, not cells in an unrelated state"
        );
    }

    #[test]
    fn machine_quantifier_avoids_referenced_native_captures() {
        let file = crate::surface::parse(
            "theorem capture(x: uint64) { ensures forall (z: uint64) { x == z }; }",
        )
        .unwrap();
        let Ensure::Proposition(proposition) = file.theorem_definitions()[0].ensures()[0].ensure()
        else {
            panic!("expected proposition")
        };
        let state = ExecutionState::new();
        for captured_variable in [1_999_999, 2_000_000, 2_000_017] {
            let captured = ProgramValue::UInt64(crate::kernel::MachineTerm::Variable(Variable(
                captured_variable,
            )));
            for embedded in [false, true] {
                let mut proposition = proposition.clone();
                if embedded {
                    let ClickProposition::ForAll { body, .. } = &mut proposition else {
                        panic!("expected forall")
                    };
                    let ClickProposition::Comparison { left, .. } = body.as_mut() else {
                        panic!("expected comparison")
                    };
                    *left = ContractExpression::ProgramExpression(ProgramExpression::Value(
                        captured.clone(),
                    ));
                }
                let lowered = elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
                    &proposition,
                    BTreeMap::new(),
                    BTreeMap::new(),
                    &state,
                    &state,
                    ProgramValueBindings::new(),
                    [("x".to_string(), captured.clone())].into_iter().collect(),
                    BTreeMap::new(),
                    &PersistentBinderMap::default(),
                    None,
                    &RecordedStates::new(),
                    SpecDefinitions::new(
                        &PredicateEnvironment::new(&[]),
                        &ClickFunctionEnvironment::new(&[]),
                    ),
                    BTreeSet::new(),
                    BTreeMap::new(),
                )
                .unwrap();
                let SpecProposition::ForAllMachineInteger { variable, body, .. } = lowered else {
                    panic!("expected machine forall")
                };
                assert_ne!(variable, Variable(captured_variable));
                let SpecProposition::Comparison { left, right, .. } = *body else {
                    panic!("expected native comparison")
                };
                assert_eq!(left, SpecExpression::Value(captured.clone()));
                assert_eq!(
                    right,
                    SpecExpression::Value(ProgramValue::UInt64(
                        crate::kernel::MachineTerm::Variable(variable)
                    ))
                );
            }
        }
    }

    #[test]
    fn integer_quantifier_stays_out_of_the_execution_band_and_avoids_caller_bindings() {
        let file = crate::surface::parse(
            "theorem capture(x: Integer) { ensures forall (z: Integer) { x == z }; }",
        )
        .unwrap();
        let Ensure::Proposition(proposition) = file.theorem_definitions()[0].ensures()[0].ensure()
        else {
            panic!("expected proposition")
        };
        let state = ExecutionState::new().with_population_creation_tracking();

        // The final execution identity must not move the quantifier allocator
        // back into the execution band's range. The first quantifier identity
        // is also captured here to ensure the binder advances past caller data.
        for captured_variable in [1_999_999, 2_000_000] {
            let integer_values = [(
                "x".to_string(),
                SpecIntegerExpression::Term(IntegerTerm::var(Variable(captured_variable))),
            )]
            .into_iter()
            .collect();
            let lowered = elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
                proposition,
                BTreeMap::new(),
                BTreeMap::new(),
                &state,
                &state,
                ProgramValueBindings::new(),
                ProgramValueBindings::new(),
                BTreeMap::new(),
                &integer_values,
                None,
                &RecordedStates::new(),
                SpecDefinitions::new(
                    &PredicateEnvironment::new(&[]),
                    &ClickFunctionEnvironment::new(&[]),
                ),
                BTreeSet::new(),
                BTreeMap::new(),
            )
            .unwrap();
            let SpecProposition::ForAllInteger { variable, body, .. } = lowered else {
                panic!("expected Integer forall")
            };
            assert_ne!(variable, Variable(captured_variable));
            assert!(
                (2_000_000..4_000_000).contains(&variable.0),
                "quantifier variable {variable:?} must stay outside the execution band"
            );
            let SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(left),
                right: SpecIntegerExpression::Term(right),
                ..
            } = *body
            else {
                panic!("expected Integer comparison")
            };
            assert_eq!(left, IntegerTerm::var(Variable(captured_variable)));
            assert_eq!(right, IntegerTerm::var(variable));
        }
    }
}

#[cfg(test)]
mod quantifier_capture_scaling_tests {
    include!(
        "../../scaling_tests/surface/lowering/annotations/quantifier_capture_scaling_tests.rs"
    );
}

#[cfg(test)]
mod local_pointer_type_index_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/surface/lowering/annotations/local_pointer_type_index_tests.rs"
        );
    }
}

#[cfg(test)]
mod old_aggregate_tests;

thread_local! {
    /// Why a function's contract could not be lowered for opaque use: the
    /// first clause's lowering error, by function name. A diagnostic only;
    /// the verdict is the contract's own.
    static OPAQUE_CONTRACT_REFUSALS: std::cell::RefCell<BTreeMap<String, String>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

fn clear_opaque_contract_refusal(function: &str) {
    OPAQUE_CONTRACT_REFUSALS.with(|refusals| {
        refusals.borrow_mut().remove(function);
    });
}

fn note_opaque_contract_refusal(function: &str, error: &impl std::fmt::Display) {
    OPAQUE_CONTRACT_REFUSALS.with(|refusals| {
        refusals
            .borrow_mut()
            .entry(function.to_string())
            .or_insert_with(|| error.to_string());
    });
}

/// `": <reason>"` when lowering `function`'s contract refused a clause, so a
/// refusal to apply the contract opaquely names the clause's own error.
pub(in crate::surface) fn opaque_contract_refusal_suffix(function: &str) -> String {
    OPAQUE_CONTRACT_REFUSALS.with(|refusals| {
        refusals
            .borrow()
            .get(function)
            .map(|reason| format!(": {reason}"))
            .unwrap_or_default()
    })
}

/// One step of a read through a call's parameter, `R.parameter(v).f[i]`.
#[derive(Clone, Copy, Debug)]
pub(in crate::surface) enum RegionParameterAccess<'a> {
    Field(&'a str),
    Index(&'a ContractExpression),
}

/// The call region, parameter and accesses of `expression` when it reads
/// through `R.parameter(v)`: a chain of fields and indexes rooted there.
pub(in crate::surface) fn region_parameter_read(
    expression: &ContractExpression,
) -> Option<(&CodeRegionRef, &str, Vec<RegionParameterAccess<'_>>)> {
    if !matches!(
        expression,
        ContractExpression::Field { .. }
            | ContractExpression::Index(..)
            | ContractExpression::ArrayIndex { .. }
    ) {
        return None;
    }
    let mut accesses = Vec::new();
    let mut current = expression;
    loop {
        match current {
            ContractExpression::Field { base, field, .. } => {
                accesses.push(RegionParameterAccess::Field(field.as_str()));
                current = base;
            }
            ContractExpression::Index(base, index) => {
                accesses.push(RegionParameterAccess::Index(index));
                current = base;
            }
            ContractExpression::ArrayIndex { base, indexes, .. } => {
                accesses.extend(indexes.iter().rev().map(RegionParameterAccess::Index));
                current = base;
            }
            ContractExpression::RegionParameter { region, name } => {
                accesses.reverse();
                return Some((region, name.as_str(), accesses));
            }
            _ => return None,
        }
    }
}

fn region_result_read(
    expression: &ContractExpression,
) -> Option<(&CodeRegionRef, Vec<RegionParameterAccess<'_>>)> {
    let mut accesses = Vec::new();
    let mut current = expression;
    loop {
        match current {
            ContractExpression::Field { base, field, .. } => {
                accesses.push(RegionParameterAccess::Field(field));
                current = base;
            }
            ContractExpression::Index(base, index) => {
                accesses.push(RegionParameterAccess::Index(index));
                current = base;
            }
            ContractExpression::RegionResult(region) if !accesses.is_empty() => {
                accesses.reverse();
                return Some((region, accesses));
            }
            _ => return None,
        }
    }
}

/// A literal element index, as written or as a C constant.
fn literal_element_index(index: &ContractExpression) -> Option<u32> {
    match index {
        ContractExpression::IntegerLiteral(value) => value.parse().ok(),
        ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::Int32(term)
            | ProgramValue::UInt32(term)
            | ProgramValue::Int64(term)
            | ProgramValue::UInt64(term),
        )) => match term {
            crate::kernel::bits32_constant!(bits)
            | crate::kernel::int64_constant!(bits)
            | crate::kernel::uint64_constant!(bits) => u32::try_from(*bits).ok(),
            _ => None,
        },
        _ => None,
    }
}
