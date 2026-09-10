use super::*;
use crate::kernel::AlgebraicValueType;

pub(super) type TypeSubstitution = BTreeMap<String, ClickType>;

pub(super) fn validate_type_parameter_list(
    kind: &str,
    name: &str,
    parameters: &[String],
) -> Result<(), ClickError> {
    let mut seen = BTreeSet::new();
    for parameter in parameters {
        if parser::is_c_type_keyword(parameter) {
            return Err(ClickError::new(format!(
                "{kind} `{name}` type parameter `{parameter}` conflicts with a built-in type"
            )));
        }
        if !seen.insert(parameter) {
            return Err(ClickError::new(format!(
                "{kind} `{name}` repeats type parameter `{parameter}`"
            )));
        }
    }
    Ok(())
}

pub(super) fn infer_type_substitution(
    kind: &str,
    name: &str,
    type_parameters: &[String],
    parameter_types: impl IntoIterator<Item = ClickType>,
    argument_types: impl IntoIterator<Item = Option<ClickType>>,
) -> Result<TypeSubstitution, String> {
    let allowed = type_parameters.iter().map(String::as_str).collect();
    let mut substitution = BTreeMap::new();
    for (parameter, argument) in parameter_types.into_iter().zip(argument_types) {
        if let Some(argument) = argument {
            unify_click_type(&parameter, &argument, &allowed, &mut substitution).map_err(
                |message| format!("cannot infer type arguments for {kind} `{name}`: {message}"),
            )?;
        }
    }
    let missing = type_parameters
        .iter()
        .filter(|parameter| !substitution.contains_key(*parameter))
        .cloned()
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(format!(
            "cannot infer type argument{} {} for {kind} `{name}`",
            if missing.len() == 1 { "" } else { "s" },
            missing.join(", ")
        ));
    }
    Ok(substitution)
}

fn unify_click_type(
    pattern: &ClickType,
    actual: &ClickType,
    allowed: &BTreeSet<&str>,
    substitution: &mut TypeSubstitution,
) -> Result<(), String> {
    match pattern {
        ClickType::Parameter(name) if allowed.contains(name.as_str()) => {
            if let Some(previous) = substitution.get(name) {
                if previous != actual {
                    return Err(format!(
                        "type parameter `{name}` is both {} and {}",
                        validation::describe_click_type(previous),
                        validation::describe_click_type(actual)
                    ));
                }
            } else {
                substitution.insert(name.clone(), actual.clone());
            }
            Ok(())
        }
        ClickType::Parameter(name) => Err(format!("unknown type parameter `{name}`")),
        ClickType::C(expected) => match actual {
            ClickType::C(actual) if validation::click_types_compatible(*actual, *expected) => {
                Ok(())
            }
            _ => Err(format!(
                "expected {}, got {}",
                validation::describe_click_type(pattern),
                validation::describe_click_type(actual)
            )),
        },
        ClickType::Algebraic(expected) => {
            let ClickType::Algebraic(actual) = actual else {
                return Err(format!(
                    "expected {}, got {}",
                    validation::describe_click_type(pattern),
                    validation::describe_click_type(actual)
                ));
            };
            if expected.rigid != actual.rigid
                || expected.name != actual.name
                || expected.arguments.len() != actual.arguments.len()
            {
                return Err(format!(
                    "expected {}, got {}",
                    validation::describe_click_type(pattern),
                    validation::describe_click_type(&ClickType::Algebraic(actual.clone()))
                ));
            }
            for (expected, actual) in expected.arguments.iter().zip(&actual.arguments) {
                unify_click_type(expected, actual, allowed, substitution)?;
            }
            Ok(())
        }
    }
}

pub(super) fn instantiate_click_type(
    click_type: &ClickType,
    substitution: &TypeSubstitution,
) -> Result<ClickType, String> {
    match click_type {
        ClickType::Parameter(name) => substitution
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unresolved type parameter `{name}`")),
        ClickType::C(c_type) => Ok(ClickType::C(*c_type)),
        ClickType::Algebraic(application) => Ok(ClickType::Algebraic(instantiate_algebraic_type(
            application,
            substitution,
        )?)),
    }
}

pub(super) fn instantiate_algebraic_type(
    application: &AlgebraicTypeApplication,
    substitution: &TypeSubstitution,
) -> Result<AlgebraicTypeApplication, String> {
    Ok(AlgebraicTypeApplication {
        rigid: application.rigid,
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| instantiate_click_type(argument, substitution))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

pub(super) fn click_type_from_algebraic_value_type(value_type: &AlgebraicValueType) -> ClickType {
    match value_type {
        AlgebraicValueType::Parameter(name) => ClickType::Algebraic(AlgebraicTypeApplication {
            rigid: true,
            name: name.clone(),
            arguments: Vec::new(),
        }),
        AlgebraicValueType::C(c_type) => ClickType::C(c0_type_from_kernel(*c_type)),
        AlgebraicValueType::Algebraic { name, arguments } => {
            ClickType::Algebraic(AlgebraicTypeApplication {
                rigid: false,
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(click_type_from_algebraic_value_type)
                    .collect(),
            })
        }
    }
}

pub(super) fn c0_type_from_kernel(c_type: CType) -> C0Type {
    match c_type {
        CType::Void => C0Type::Void,
        CType::Bool => C0Type::Bool,
        CType::VoidPointer => C0Type::VoidPointer,
        CType::Int16 => C0Type::Int16,
        CType::Int32 => C0Type::Int32,
        CType::UInt8 => C0Type::UInt8,
        CType::UInt16 => C0Type::UInt16,
        CType::UInt32 => C0Type::UInt32,
        CType::Int64 => C0Type::Int64,
        CType::UInt64 => C0Type::UInt64,
        CType::Float32 => C0Type::Float32,
        CType::Float64 => C0Type::Float64,
        CType::Int16Pointer => C0Type::Int16Pointer,
        CType::UInt16Pointer => C0Type::UInt16Pointer,
        CType::Int32Pointer => C0Type::Int32Pointer,
        CType::UInt8Pointer => C0Type::UInt8Pointer,
        CType::UInt32Pointer => C0Type::UInt32Pointer,
        CType::Int64Pointer => C0Type::Int64Pointer,
        CType::UInt64Pointer => C0Type::UInt64Pointer,
        CType::Float32Pointer => C0Type::Float32Pointer,
        CType::Float64Pointer => C0Type::Float64Pointer,
        CType::Int16PointerPointer => C0Type::Int16PointerPointer,
        CType::UInt16PointerPointer => C0Type::UInt16PointerPointer,
        CType::Int32PointerPointer => C0Type::Int32PointerPointer,
        CType::UInt8PointerPointer => C0Type::UInt8PointerPointer,
        CType::UInt32PointerPointer => C0Type::UInt32PointerPointer,
        CType::Int64PointerPointer => C0Type::Int64PointerPointer,
        CType::UInt64PointerPointer => C0Type::UInt64PointerPointer,
        CType::Float32PointerPointer => C0Type::Float32PointerPointer,
        CType::Float64PointerPointer => C0Type::Float64PointerPointer,
        CType::FunctionPointer(signature) => C0Type::FunctionPointer(signature),
        CType::Int16Array(length) => C0Type::Int16Array(length),
        CType::UInt16Array(length) => C0Type::UInt16Array(length),
        CType::Int32Array(length) => C0Type::Int32Array(length),
        CType::UInt8Array(length) => C0Type::UInt8Array(length),
        CType::UInt32Array(length) => C0Type::UInt32Array(length),
        CType::Int64Array(length) => C0Type::Int64Array(length),
        CType::UInt64Array(length) => C0Type::UInt64Array(length),
        CType::Float32Array(length) => C0Type::Float32Array(length),
        CType::Float64Array(length) => C0Type::Float64Array(length),
    }
}

pub(super) fn instance_name(
    name: &str,
    type_parameters: &[String],
    substitution: &TypeSubstitution,
) -> Result<String, String> {
    fn type_identity(ty: &ClickType) -> String {
        match ty {
            ClickType::Algebraic(application) if application.rigid => {
                format!("[rigid {}]", application.name)
            }
            ClickType::Algebraic(application) if !application.arguments.is_empty() => format!(
                "{}<{}>",
                application.name,
                application
                    .arguments
                    .iter()
                    .map(type_identity)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            _ => validation::describe_click_type(ty),
        }
    }
    if type_parameters.is_empty() {
        return Ok(name.to_string());
    }
    let arguments = type_parameters
        .iter()
        .map(|parameter| {
            substitution
                .get(parameter)
                .map(type_identity)
                .ok_or_else(|| format!("unresolved type parameter `{parameter}`"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(format!("{name}::<{}>", arguments.join(", ")))
}

pub(super) fn instantiate_function(
    definition: &ClickFunctionDefinition,
    substitution: &TypeSubstitution,
) -> Result<ClickFunctionDefinition, String> {
    Ok(ClickFunctionDefinition {
        name: instance_name(
            definition.name(),
            definition.type_parameters(),
            substitution,
        )?,
        type_parameters: Vec::new(),
        parameters: definition
            .parameters()
            .iter()
            .map(|parameter| instantiate_parameter(parameter, substitution))
            .collect::<Result<Vec<_>, _>>()?,
        return_type: instantiate_click_type(definition.return_type(), substitution)?,
        decreases: definition
            .decreases()
            .map(|expression| instantiate_expression(expression, substitution))
            .transpose()?,
        body: instantiate_expression(definition.body(), substitution)?,
    })
}

pub(super) fn instantiate_function_for_surface_call_with_variables(
    definition: &ClickFunctionDefinition,
    arguments: &[ContractExpression],
    variables: &BTreeMap<String, ClickType>,
) -> Result<ClickFunctionDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(definition.clone());
    }
    let argument_types = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| match parameter.click_type() {
            ClickType::C(c_type) => Some(ClickType::C(*c_type)),
            ClickType::Algebraic(_) | ClickType::Parameter(_) => {
                syntactic_expression_type(argument, variables)
            }
        })
        .collect::<Vec<_>>();
    let substitution = infer_type_substitution(
        "function",
        definition.name(),
        definition.type_parameters(),
        definition
            .parameters()
            .iter()
            .map(|parameter| parameter.click_type().clone()),
        argument_types,
    )?;
    instantiate_function(definition, &substitution)
}

fn syntactic_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, ClickType>,
) -> Option<ClickType> {
    match expression {
        ContractExpression::AlgebraicVariable { algebraic_type, .. }
        | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
            Some(ClickType::Algebraic(algebraic_type.clone()))
        }
        ContractExpression::CFragment(CExpression::Value(value)) => {
            Some(ClickType::C(c0_type_from_kernel(value.c_type())))
        }
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => {
            variables.get(name).cloned()
        }
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => syntactic_expression_type(inner, variables),
        ContractExpression::Let { body, .. } => syntactic_expression_type(body, variables),
        _ => None,
    }
}

pub(super) fn concrete_variable_types(
    values: &BTreeMap<String, CValue>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
) -> BTreeMap<String, ClickType> {
    values
        .iter()
        .map(|(name, value)| {
            (
                name.clone(),
                ClickType::C(c0_type_from_kernel(value.c_type())),
            )
        })
        .chain(algebraic_values.iter().map(|(name, value)| {
            (
                name.clone(),
                click_type_from_algebraic_value_type(&value.algebraic_type.value_type()),
            )
        }))
        .collect()
}

pub(super) fn instantiate_predicate(
    definition: &PredicateDefinition,
    substitution: &TypeSubstitution,
) -> Result<PredicateDefinition, String> {
    Ok(PredicateDefinition {
        name: instance_name(
            definition.name(),
            definition.type_parameters(),
            substitution,
        )?,
        type_parameters: Vec::new(),
        parameters: definition
            .parameters()
            .iter()
            .map(|parameter| instantiate_parameter(parameter, substitution))
            .collect::<Result<Vec<_>, _>>()?,
        body: instantiate_proposition(definition.body(), substitution)?,
    })
}

pub(super) fn instantiate_predicate_for_surface_call(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
    variables: &BTreeMap<String, ClickType>,
) -> Result<PredicateDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(definition.clone());
    }
    let argument_types = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| match parameter.click_type() {
            ClickType::C(c_type) => Some(ClickType::C(*c_type)),
            ClickType::Algebraic(_) | ClickType::Parameter(_) => {
                syntactic_expression_type(argument, variables)
            }
        })
        .collect::<Vec<_>>();
    let substitution = infer_type_substitution(
        "predicate",
        definition.name(),
        definition.type_parameters(),
        definition
            .parameters()
            .iter()
            .map(|parameter| parameter.click_type().clone()),
        argument_types,
    )?;
    instantiate_predicate(definition, &substitution)
}

pub(super) fn instantiate_theorem(
    definition: &TheoremDefinition,
    substitution: &TypeSubstitution,
) -> Result<TheoremDefinition, String> {
    let parameters = definition
        .parameters()
        .iter()
        .map(|parameter| instantiate_parameter(parameter, substitution))
        .collect::<Result<Vec<_>, _>>()?;
    let algebraic_parameters = parameters
        .iter()
        .enumerate()
        .filter_map(|(binder_index, parameter)| {
            let ClickType::Algebraic(algebraic_type) = parameter.click_type() else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ContractExpression::AlgebraicVariable {
                    name: parameter.name().to_string(),
                    algebraic_type: algebraic_type.clone(),
                    binder_index,
                },
            ))
        })
        .collect::<BTreeMap<_, _>>();
    Ok(TheoremDefinition {
        executes: definition.executes.clone(),
        name: instance_name(
            definition.name(),
            definition.type_parameters(),
            substitution,
        )?,
        type_parameters: Vec::new(),
        parameters,
        requires: definition
            .requires()
            .iter()
            .map(|requirement| {
                instantiate_requirement(requirement, substitution, &algebraic_parameters)
            })
            .collect::<Result<Vec<_>, _>>()?,
        ensures: definition
            .ensures()
            .iter()
            .map(|ensure| instantiate_ensure_clause(ensure, substitution, &algebraic_parameters))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn instantiate_requirement(
    requirement: &Requirement,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<Requirement, String> {
    Ok(match requirement {
        Requirement::Labeled { label, requirement } => Requirement::Labeled {
            label: label.clone(),
            requirement: Box::new(instantiate_requirement(
                requirement,
                substitution,
                algebraic_parameters,
            )?),
        },
        Requirement::Proposition(proposition) => {
            Requirement::Proposition(substitute_click_proposition(
                &instantiate_proposition(proposition, substitution)?,
                algebraic_parameters,
            )?)
        }
        requirement => requirement.clone(),
    })
}

fn instantiate_ensure_clause(
    ensure: &EnsureClause,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<EnsureClause, String> {
    let ensure_value = match ensure.ensure() {
        Ensure::Proposition(proposition) => Ensure::Proposition(substitute_click_proposition(
            &instantiate_proposition(proposition, substitution)?,
            algebraic_parameters,
        )?),
        resource @ Ensure::Resource(_) => resource.clone(),
    };
    Ok(EnsureClause {
        name: ensure.name.clone(),
        ensure: ensure_value,
        proof: instantiate_source_proof(ensure.proof(), substitution, algebraic_parameters)?,
        borrowed: ensure.borrowed,
    })
}

fn instantiate_source_proof(
    proof: &SourceProof,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<SourceProof, String> {
    Ok(match proof {
        SourceProof::Default => SourceProof::Default,
        SourceProof::Tactic(tactic) => SourceProof::Tactic(*tactic),
        SourceProof::Script(tactics) => SourceProof::Script(
            tactics
                .iter()
                .map(|tactic| instantiate_proof_tactic(tactic, substitution, algebraic_parameters))
                .collect::<Result<Vec<_>, _>>()?,
        ),
    })
}

fn instantiate_theorem_application(
    application: &TheoremApplication,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<TheoremApplication, String> {
    Ok(TheoremApplication {
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| {
                substitute_contract_expression(
                    &instantiate_expression(argument, substitution)?,
                    algebraic_parameters,
                )
            })
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn instantiate_function_application(
    application: &ClickFunctionApplication,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<ClickFunctionApplication, String> {
    Ok(ClickFunctionApplication {
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| {
                substitute_contract_expression(
                    &instantiate_expression(argument, substitution)?,
                    algebraic_parameters,
                )
            })
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn instantiate_proof_tactics(
    tactics: &[ProofTactic],
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<Vec<ProofTactic>, String> {
    tactics
        .iter()
        .map(|tactic| instantiate_proof_tactic(tactic, substitution, algebraic_parameters))
        .collect()
}

fn instantiate_proof_tactic(
    tactic: &ProofTactic,
    substitution: &TypeSubstitution,
    algebraic_parameters: &BTreeMap<String, ContractExpression>,
) -> Result<ProofTactic, String> {
    let expression = |value: &ContractExpression| {
        substitute_contract_expression(
            &instantiate_expression(value, substitution)?,
            algebraic_parameters,
        )
    };
    let proposition = |value: &ClickProposition| {
        substitute_click_proposition(
            &instantiate_proposition(value, substitution)?,
            algebraic_parameters,
        )
    };
    Ok(match tactic {
        ProofTactic::Match(proof_match) => ProofTactic::Match(Box::new(ProofMatch {
            scrutinee: expression(&proof_match.scrutinee)?,
            arms: proof_match
                .arms
                .iter()
                .map(|arm| {
                    let mut scoped_parameters = algebraic_parameters.clone();
                    for binding in &arm.bindings {
                        scoped_parameters.remove(binding);
                    }
                    Ok(ProofInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        tactics: instantiate_proof_tactics(
                            &arm.tactics,
                            substitution,
                            &scoped_parameters,
                        )?,
                    })
                })
                .collect::<Result<_, String>>()?,
        })),
        ProofTactic::UnfoldFunction(application) => ProofTactic::UnfoldFunction(
            instantiate_function_application(application, substitution, algebraic_parameters)?,
        ),
        ProofTactic::StructuralInduct {
            parameter,
            hypothesis,
            arms,
        } => ProofTactic::StructuralInduct {
            parameter: parameter.clone(),
            hypothesis: hypothesis.clone(),
            arms: arms
                .iter()
                .map(|arm| {
                    let mut scoped_parameters = algebraic_parameters.clone();
                    for binding in &arm.bindings {
                        scoped_parameters.remove(binding);
                    }
                    Ok(ProofInductionArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        tactics: instantiate_proof_tactics(
                            &arm.tactics,
                            substitution,
                            &scoped_parameters,
                        )?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?,
        },
        ProofTactic::ApplyInduction {
            hypothesis,
            argument,
        } => ProofTactic::ApplyInduction {
            hypothesis: hypothesis.clone(),
            argument: expression(argument)?,
        },
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            argument,
            premises,
        } => ProofTactic::ApplyInductionUsing {
            hypothesis: hypothesis.clone(),
            argument: expression(argument)?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::ApplyTheorem(application) => ProofTactic::ApplyTheorem(
            instantiate_theorem_application(application, substitution, algebraic_parameters)?,
        ),
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => ProofTactic::ApplyTheoremUsing {
            application: instantiate_theorem_application(
                application,
                substitution,
                algebraic_parameters,
            )?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::Have(have) => ProofTactic::Have(ProofHave {
            proposition: proposition(&have.proposition)?,
            proof: instantiate_source_proof(&have.proof, substitution, algebraic_parameters)?,
        }),
        ProofTactic::If(proof_if) => ProofTactic::If(ProofIf {
            condition: proposition(&proof_if.condition)?,
            then_tactics: instantiate_proof_tactics(
                &proof_if.then_tactics,
                substitution,
                algebraic_parameters,
            )?,
            else_tactics: instantiate_proof_tactics(
                &proof_if.else_tactics,
                substitution,
                algebraic_parameters,
            )?,
        }),
        ProofTactic::CloseInvariantsBy(body) => ProofTactic::CloseInvariantsBy(
            instantiate_proof_tactics(body, substitution, algebraic_parameters)?,
        ),
        ProofTactic::Both(both) => ProofTactic::Both(ProofBoth {
            left_tactics: instantiate_proof_tactics(
                &both.left_tactics,
                substitution,
                algebraic_parameters,
            )?,
            right_tactics: instantiate_proof_tactics(
                &both.right_tactics,
                substitution,
                algebraic_parameters,
            )?,
        }),
        ProofTactic::Cases(cases) => ProofTactic::Cases(ProofCases {
            disjunction: proposition(&cases.disjunction)?,
            left_tactics: instantiate_proof_tactics(
                &cases.left_tactics,
                substitution,
                algebraic_parameters,
            )?,
            right_tactics: instantiate_proof_tactics(
                &cases.right_tactics,
                substitution,
                algebraic_parameters,
            )?,
        }),
        ProofTactic::Extract(value) => ProofTactic::Extract(proposition(value)?),
        ProofTactic::ArithmeticUsing(premises) => ProofTactic::ArithmeticUsing(
            premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ProofTactic::NormalizeUsing(premises) => ProofTactic::NormalizeUsing(
            premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ProofTactic::Contradiction(value) => ProofTactic::Contradiction(proposition(value)?),
        ProofTactic::Rewrite(value) => ProofTactic::Rewrite(proposition(value)?),
        ProofTactic::Transport { source, target } => ProofTactic::Transport {
            source: proposition(source)?,
            target: proposition(target)?,
        },
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => ProofTactic::TransportUsing {
            source: proposition(source)?,
            target: proposition(target)?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::InstantiateUsing {
            quantified,
            argument,
            premises,
        } => ProofTactic::InstantiateUsing {
            quantified: proposition(quantified)?,
            argument: expression(argument)?,
            premises: premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ProofTactic::SimpUsing(using) => ProofTactic::SimpUsing(ProofSimpUsing {
            premises: using
                .premises
                .iter()
                .map(proposition)
                .collect::<Result<Vec<_>, _>>()?,
        }),
        tactic => tactic.clone(),
    })
}

fn instantiate_parameter(
    parameter: &FunctionParameter,
    substitution: &TypeSubstitution,
) -> Result<FunctionParameter, String> {
    Ok(FunctionParameter {
        click_type: instantiate_click_type(parameter.click_type(), substitution)?,
        name: parameter.name.clone(),
        struct_name: parameter.struct_name.clone(),
        function_pointer_signature: parameter.function_pointer_signature.clone(),
        constant: parameter.constant,
        pointee_constant: parameter.pointee_constant,
    })
}

fn instantiate_expression(
    expression: &ContractExpression,
    substitution: &TypeSubstitution,
) -> Result<ContractExpression, String> {
    let recurse =
        |expression: &ContractExpression| instantiate_expression(expression, substitution);
    Ok(match expression {
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => ContractExpression::AlgebraicConstructor {
            algebraic_type: instantiate_algebraic_type(algebraic_type, substitution)?,
            variant: variant.clone(),
            arguments: arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        },
        ContractExpression::AlgebraicVariable {
            name,
            algebraic_type,
            binder_index,
        } => ContractExpression::AlgebraicVariable {
            name: name.clone(),
            algebraic_type: instantiate_algebraic_type(algebraic_type, substitution)?,
            binder_index: *binder_index,
        },
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            ContractExpression::AlgebraicMatch {
                scrutinee: Box::new(recurse(scrutinee)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(AlgebraicMatchArm {
                            type_name: arm.type_name.clone(),
                            variant: arm.variant.clone(),
                            bindings: arm.bindings.clone(),
                            body: recurse(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?,
            }
        }
        ContractExpression::SequenceLiteral(elements) => ContractExpression::SequenceLiteral(
            elements.iter().map(recurse).collect::<Result<_, _>>()?,
        ),
        ContractExpression::SequenceConcat(left, right) => {
            ContractExpression::SequenceConcat(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Old(inner) => ContractExpression::Old(Box::new(recurse(inner)?)),
        ContractExpression::At {
            selector,
            expression,
        } => ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(recurse(expression)?),
        },
        ContractExpression::Add(left, right) => {
            ContractExpression::Add(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Subtract(left, right) => {
            ContractExpression::Subtract(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Multiply(left, right) => {
            ContractExpression::Multiply(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Divide(left, right) => {
            ContractExpression::Divide(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Remainder(left, right) => {
            ContractExpression::Remainder(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::ShiftLeft(left, right) => {
            ContractExpression::ShiftLeft(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::ShiftRight(left, right) => {
            ContractExpression::ShiftRight(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseAnd(left, right) => {
            ContractExpression::BitwiseAnd(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseOr(left, right) => {
            ContractExpression::BitwiseOr(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseXor(left, right) => {
            ContractExpression::BitwiseXor(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::Index(left, right) => {
            ContractExpression::Index(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ContractExpression::BitwiseNot(inner) => {
            ContractExpression::BitwiseNot(Box::new(recurse(inner)?))
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => ContractExpression::If {
            condition: Box::new(instantiate_proposition(condition, substitution)?),
            then_branch: Box::new(recurse(then_branch)?),
            else_branch: Box::new(recurse(else_branch)?),
        },
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => ContractExpression::RangeFold {
            start: Box::new(recurse(start)?),
            end: Box::new(recurse(end)?),
            initial: Box::new(recurse(initial)?),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(recurse(body)?),
        },
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => ContractExpression::Let {
            name: name.clone(),
            click_type: click_type
                .as_ref()
                .map(|click_type| instantiate_click_type(click_type, substitution))
                .transpose()?,
            value: Box::new(recurse(value)?),
            body: Box::new(recurse(body)?),
        },
        ContractExpression::Call { name, arguments } => ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        },
        expression => expression.clone(),
    })
}

fn instantiate_proposition(
    proposition: &ClickProposition,
    substitution: &TypeSubstitution,
) -> Result<ClickProposition, String> {
    let expression =
        |expression: &ContractExpression| instantiate_expression(expression, substitution);
    let recurse =
        |proposition: &ClickProposition| instantiate_proposition(proposition, substitution);
    Ok(match proposition {
        ClickProposition::Comparison {
            operator,
            left,
            right,
        } => ClickProposition::Comparison {
            operator: *operator,
            left: expression(left)?,
            right: expression(right)?,
        },
        ClickProposition::FloatClassification {
            classification,
            expression: value,
        } => ClickProposition::FloatClassification {
            classification: *classification,
            expression: expression(value)?,
        },
        ClickProposition::Defined { expression: value } => ClickProposition::Defined {
            expression: expression(value)?,
        },
        ClickProposition::At {
            selector,
            proposition,
        } => ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(recurse(proposition)?),
        },
        ClickProposition::And(left, right) => {
            ClickProposition::And(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ClickProposition::Or(left, right) => {
            ClickProposition::Or(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ClickProposition::Not(body) => ClickProposition::Not(Box::new(recurse(body)?)),
        ClickProposition::Implies(left, right) => {
            ClickProposition::Implies(Box::new(recurse(left)?), Box::new(recurse(right)?))
        }
        ClickProposition::ForAll { c_type, name, body } => ClickProposition::ForAll {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::Exists { c_type, name, body } => ClickProposition::Exists {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => ClickProposition::RangeAll {
            start: expression(start)?,
            end: expression(end)?,
            item: item.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => ClickProposition::RangeAny {
            start: expression(start)?,
            end: expression(end)?,
            item: item.clone(),
            body: Box::new(recurse(body)?),
        },
        ClickProposition::PredicateCall { name, arguments } => ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(expression)
                .collect::<Result<Vec<_>, _>>()?,
        },
        proposition => proposition.clone(),
    })
}
