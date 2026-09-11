use super::*;
use crate::kernel::AlgebraicValueType;
use crate::kernel::c_function_contract_refinement_obligations;

const STRUCTURAL_INDUCTION_VARIABLE_BASE: u64 = 1 << 60;

mod execution_theorems;
use execution_theorems::verify_execution_theorem;

pub(in crate::surface) fn verify_theorem_definitions(
    theorem_definitions: &[TheoremDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
    resource_environment: &ResourceEnvironment,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = TheoremEnvironment::new(&[]);
    for theorem in theorem_definitions {
        if theorem.executes.is_some() {
            verified.push(verify_execution_theorem(
                theorem,
                predicate_environment,
                click_function_environment,
                &theorem_environment,
                function_environment,
                resource_environment,
            )?);
            theorem_environment.insert(theorem.clone());
            continue;
        }
        {
            let mut symbolic;
            let checked = if theorem.type_parameters().is_empty() {
                theorem
            } else {
                let substitution = theorem
                    .type_parameters()
                    .iter()
                    .map(|name| {
                        (
                            name.clone(),
                            ClickType::Algebraic(AlgebraicTypeApplication {
                                rigid: true,
                                name: name.clone(),
                                arguments: Vec::new(),
                            }),
                        )
                    })
                    .collect();
                symbolic = generics::instantiate_theorem(theorem, &substitution)
                    .map_err(ClickError::new)?;
                symbolic.name = theorem.name().to_string();
                &symbolic
            };
            verified.extend(verify_concrete_theorem_definition(
                checked,
                predicate_environment,
                click_function_environment,
                &theorem_environment,
                function_environment,
            )?);
        }
        theorem_environment.insert(theorem.clone());
    }
    Ok(verified)
}

pub(in crate::surface) fn verify_concrete_theorem_definition(
    theorem: &TheoremDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    debug_assert!(theorem.type_parameters().is_empty());
    let context = pure_theorem_context(theorem, predicate_environment, click_function_environment)?;
    theorem
        .ensures()
        .iter()
        .enumerate()
        .map(|(ensure_index, ensure_clause)| {
            let claim_label = theorem_claim_label(theorem.name(), ensure_index, ensure_clause);
            verify_theorem_ensure(
                theorem,
                ensure_index,
                ensure_clause,
                &claim_label,
                &context,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                function_environment,
            )
        })
        .collect()
}

#[derive(Clone, Debug)]
pub(super) struct PureTheoremContext {
    pub(super) memory: CMemory,
    pub(super) values: BTreeMap<String, CValue>,
    pub(super) integer_values:
        crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    pub(super) array_refs: ClickArrayRefs,
    pub(super) requires: Vec<Proposition>,
    pub(super) surface_requirements: SurfacePropositionMap,
}

#[derive(Clone, Debug)]
pub(super) struct PureInductionSetup {
    pub(super) parameter: String,
    pub(super) hypothesis: String,
    pub(super) surface_requires: Vec<ClickProposition>,
    pub(super) surface_goal: ClickProposition,
}

#[derive(Clone, Debug)]
pub(super) struct PureStructuralInductionApplication {
    pub(super) argument: ContractExpression,
    pub(super) surface_premises: Vec<ClickProposition>,
    pub(super) kernel_premises: Vec<Proposition>,
    pub(super) implication: Proposition,
    pub(super) conclusion: Proposition,
}

#[derive(Clone, Debug)]
pub(super) struct PureStructuralInductionBranchSetup {
    pub(super) hypothesis: String,
    pub(super) applications: Vec<PureStructuralInductionApplication>,
    pub(super) algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
}

pub(super) fn pure_induction_hypothesis(
    setup: &PureInductionSetup,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let Some(CValue::Int32(Bitvector32Term::Variable(current_variable))) =
        context.values.get(&setup.parameter)
    else {
        return Err(ClickError::new("invalid int32 induction parameter"));
    };
    let opaque_goal = lower_pure_theorem_proposition_opaque(
        &setup.hypothesis,
        &setup.surface_goal,
        &context.values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(ClickError::new)?;
    let opaque_requirements = setup
        .surface_requires
        .iter()
        .map(|requirement| {
            lower_pure_theorem_proposition_opaque(
                &setup.hypothesis,
                requirement,
                &context.values,
                &context.array_refs,
                &context.memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(ClickError::new)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut propositions = opaque_requirements.clone();
    propositions.push(opaque_goal.clone());
    let variable = fresh_int32_variable_for_propositions(&propositions);
    let value = Bitvector32Term::Variable(variable);
    let substitute = |proposition: &Proposition| {
        substitute_int32_variable_in_proposition(proposition, *current_variable, value.clone())
    };
    let mut body = substitute(&opaque_goal);
    for requirement in opaque_requirements.iter().rev() {
        let requirement = substitute(requirement);
        body = Proposition::Implies(Box::new(requirement), Box::new(body));
    }
    let smaller = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(value.clone()),
            Box::new(Bitvector32Term::Variable(*current_variable)),
        ),
        true,
    );
    body = Proposition::Implies(Box::new(smaller), Box::new(body));
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(value),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    body = Proposition::Implies(Box::new(nonnegative), Box::new(body));
    Ok(Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(body),
    })
}

fn prepare_pure_induction_tactics(
    theorem: &TheoremDefinition,
    goal: &ClickProposition,
    tactics: &[ProofTactic],
) -> Result<(Vec<ProofTactic>, Option<PureInductionSetup>), ClickError> {
    let Some(ProofTactic::Induct {
        parameter,
        hypothesis,
    }) = tactics.first()
    else {
        if tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Induct { .. }))
        {
            return Err(ClickError::new(
                "`induct` must be the first tactic in a pure theorem proof",
            ));
        }
        return Ok((tactics.to_vec(), None));
    };
    if !theorem
        .parameters()
        .iter()
        .any(|candidate| candidate.name() == parameter && candidate.c_type() == C0Type::Int32)
    {
        return Err(ClickError::new(format!(
            "`induct({parameter})` requires an int32 theorem parameter with that name"
        )));
    }
    let surface_requires = theorem
        .requires()
        .iter()
        .map(|requirement| {
            requirement.proposition().cloned().ok_or_else(|| {
                ClickError::new("pure induction supports proposition requirements only")
            })
        })
        .collect::<Result<Vec<_>, _>>()?;

    fn transform(
        tactics: &[ProofTactic],
        hypothesis: &str,
    ) -> Result<Vec<ProofTactic>, ClickError> {
        tactics
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::Induct { .. } => Err(ClickError::new(
                    "a pure theorem proof may contain only one top-level `induct` tactic",
                )),
                ProofTactic::ApplyTheorem(application) if application.name == hypothesis => {
                    let [argument] = application.arguments.as_slice() else {
                        return Err(ClickError::new(format!(
                            "induction hypothesis `{hypothesis}` expects one argument"
                        )));
                    };
                    Ok(ProofTactic::ApplyInduction {
                        hypothesis: hypothesis.to_string(),
                        argument: argument.clone(),
                    })
                }
                ProofTactic::ApplyTheoremUsing {
                    application,
                    premises,
                } if application.name == hypothesis => {
                    let [argument] = application.arguments.as_slice() else {
                        return Err(ClickError::new(format!(
                            "induction hypothesis `{hypothesis}` expects one argument"
                        )));
                    };
                    Ok(ProofTactic::ApplyInductionUsing {
                        hypothesis: hypothesis.to_string(),
                        argument: argument.clone(),
                        premises: premises.clone(),
                    })
                }
                ProofTactic::If(proof_if) => Ok(ProofTactic::If(ProofIf {
                    condition: proof_if.condition.clone(),
                    then_tactics: transform(&proof_if.then_tactics, hypothesis)?,
                    else_tactics: transform(&proof_if.else_tactics, hypothesis)?,
                })),
                ProofTactic::Both(both) => Ok(ProofTactic::Both(ProofBoth {
                    left_tactics: transform(&both.left_tactics, hypothesis)?,
                    right_tactics: transform(&both.right_tactics, hypothesis)?,
                })),
                ProofTactic::Cases(proof_cases) => Ok(ProofTactic::Cases(ProofCases {
                    disjunction: proof_cases.disjunction.clone(),
                    left_tactics: transform(&proof_cases.left_tactics, hypothesis)?,
                    right_tactics: transform(&proof_cases.right_tactics, hypothesis)?,
                })),
                ProofTactic::ApplyInduction { .. } | ProofTactic::ApplyInductionUsing { .. } => {
                    Err(ClickError::new(
                        "internal induction-application syntax is not accepted directly",
                    ))
                }
                tactic => Ok(tactic.clone()),
            })
            .collect()
    }

    let mut prepared = vec![tactics[0].clone()];
    prepared.extend(transform(&tactics[1..], hypothesis)?);
    Ok((
        prepared,
        Some(PureInductionSetup {
            parameter: parameter.clone(),
            hypothesis: hypothesis.clone(),
            surface_requires,
            surface_goal: goal.clone(),
        }),
    ))
}

pub(super) fn click_type_from_algebraic_value_type(
    value_type: &AlgebraicValueType,
) -> Result<ClickType, ClickError> {
    Ok(match value_type {
        AlgebraicValueType::Integer => ClickType::Integer,
        AlgebraicValueType::C(c_type) => ClickType::C(match c_type {
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
            CType::FunctionPointer(signature) => C0Type::FunctionPointer(*signature),
            CType::Int16Array(length) => C0Type::Int16Array(*length),
            CType::UInt16Array(length) => C0Type::UInt16Array(*length),
            CType::Int32Array(length) => C0Type::Int32Array(*length),
            CType::UInt8Array(length) => C0Type::UInt8Array(*length),
            CType::UInt32Array(length) => C0Type::UInt32Array(*length),
            CType::Int64Array(length) => C0Type::Int64Array(*length),
            CType::UInt64Array(length) => C0Type::UInt64Array(*length),
            CType::Float32Array(length) => C0Type::Float32Array(*length),
            CType::Float64Array(length) => C0Type::Float64Array(*length),
        }),
        AlgebraicValueType::Parameter(name) => ClickType::Algebraic(AlgebraicTypeApplication {
            rigid: true,
            name: name.clone(),
            arguments: Vec::new(),
        }),
        AlgebraicValueType::Algebraic { name, arguments } => {
            ClickType::Algebraic(AlgebraicTypeApplication {
                rigid: false,
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(click_type_from_algebraic_value_type)
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    })
}

fn prepare_structural_induction_arm_tactics(
    tactics: &[ProofTactic],
    setup: &PureStructuralInductionBranchSetup,
    bindings: &BTreeMap<String, ContractExpression>,
) -> Result<Vec<ProofTactic>, ClickError> {
    tactics
        .iter()
        .map(|tactic| match tactic {
            ProofTactic::ApplyTheorem(application) if application.name == setup.hypothesis => {
                let [argument] = application.arguments.as_slice() else {
                    return Err(ClickError::new(format!(
                        "induction hypothesis `{}` expects one argument",
                        setup.hypothesis
                    )));
                };
                let Some(selected) = setup
                    .applications
                    .iter()
                    .find(|candidate| candidate.argument == *argument)
                else {
                    return Err(ClickError::new(
                        "structural induction hypothesis expects an immediate recursive field",
                    ));
                };
                Ok(ProofTactic::ApplyInductionUsing {
                    hypothesis: setup.hypothesis.clone(),
                    argument: argument.clone(),
                    premises: selected.surface_premises.clone(),
                })
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } if application.name == setup.hypothesis => {
                let [argument] = application.arguments.as_slice() else {
                    return Err(ClickError::new(format!(
                        "induction hypothesis `{}` expects one argument",
                        setup.hypothesis
                    )));
                };
                Ok(ProofTactic::ApplyInductionUsing {
                    hypothesis: setup.hypothesis.clone(),
                    argument: argument.clone(),
                    premises: premises.clone(),
                })
            }
            ProofTactic::If(proof_if) => Ok(ProofTactic::If(ProofIf {
                condition: proof_if.condition.clone(),
                then_tactics: prepare_structural_induction_arm_tactics(
                    &proof_if.then_tactics,
                    setup,
                    bindings,
                )?,
                else_tactics: prepare_structural_induction_arm_tactics(
                    &proof_if.else_tactics,
                    setup,
                    bindings,
                )?,
            })),
            ProofTactic::Both(both) => Ok(ProofTactic::Both(ProofBoth {
                left_tactics: prepare_structural_induction_arm_tactics(
                    &both.left_tactics,
                    setup,
                    bindings,
                )?,
                right_tactics: prepare_structural_induction_arm_tactics(
                    &both.right_tactics,
                    setup,
                    bindings,
                )?,
            })),
            ProofTactic::Cases(proof_cases) => Ok(ProofTactic::Cases(ProofCases {
                disjunction: proof_cases.disjunction.clone(),
                left_tactics: prepare_structural_induction_arm_tactics(
                    &proof_cases.left_tactics,
                    setup,
                    bindings,
                )?,
                right_tactics: prepare_structural_induction_arm_tactics(
                    &proof_cases.right_tactics,
                    setup,
                    bindings,
                )?,
            })),
            ProofTactic::StructuralInduct { .. } | ProofTactic::Induct { .. } => Err(
                ClickError::new("nested induction is not supported in a structural induction arm"),
            ),
            ProofTactic::ApplyInduction { .. } | ProofTactic::ApplyInductionUsing { .. } => Err(
                ClickError::new("internal induction-application syntax is not accepted directly"),
            ),
            ProofTactic::ApplyTheorem(application)
            | ProofTactic::ApplyTheoremUsing { application, .. } => {
                // Ordinary applications use the same typed symbolic fields as
                // the branch goal, including in their checked explicit form.
                let mut application = application.clone();
                application.arguments = application
                    .arguments
                    .iter()
                    .map(|argument| {
                        substitute_contract_expression(argument, bindings).map_err(ClickError::new)
                    })
                    .collect::<Result<_, _>>()?;
                Ok(match tactic {
                    ProofTactic::ApplyTheoremUsing { premises, .. } => {
                        ProofTactic::ApplyTheoremUsing {
                            application,
                            premises: premises.clone(),
                        }
                    }
                    _ => ProofTactic::ApplyTheorem(application),
                })
            }
            tactic => Ok(tactic.clone()),
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn check_pure_structural_induction(
    theorem: &TheoremDefinition,
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
) -> Result<ProofCertificate, ClickError> {
    let [
        ProofTactic::StructuralInduct {
            parameter,
            hypothesis,
            arms,
        },
    ] = tactics
    else {
        return Err(ClickError::new(
            "structural `induct` must be the only top-level tactic in a pure theorem proof",
        ));
    };
    let Some((parameter_index, parameter_definition)) = theorem
        .parameters()
        .iter()
        .enumerate()
        .find(|(_, candidate)| candidate.name() == parameter)
    else {
        return Err(ClickError::new(format!(
            "`induct({parameter})` requires a theorem parameter with that name"
        )));
    };
    let ClickType::Algebraic(parameter_type) = parameter_definition.click_type() else {
        return Err(ClickError::new(format!(
            "constructor-branching `induct({parameter})` requires an algebraic theorem parameter"
        )));
    };
    let parameter_expression = ContractExpression::AlgebraicVariable {
        // Arbitrary types have no exhaustive constructor schema.
        name: parameter.clone(),
        algebraic_type: parameter_type.clone(),
        binder_index: parameter_index,
    };
    if parameter_type.rigid {
        return Err(ClickError::new(format!(
            "`{claim_label}`: structural induction requires a datatype, not arbitrary type `{}`",
            parameter_type.name
        )));
    }
    let state = CState::new().with_memory(context.memory.clone());
    let parameter_value = capture_fixed_state_algebraic_expression(
        &parameter_expression,
        &PureFactContext::new(),
        &context.values,
        &context.array_refs,
        &state,
        &state,
        None,
        &RecordedSnapshots::new(),
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    let root_value_type = AlgebraicValueType::Algebraic {
        name: parameter_value.algebraic_type.name.clone(),
        arguments: parameter_value.algebraic_type.arguments.clone(),
    };
    let theorem_parameter_names = theorem
        .parameters()
        .iter()
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    let mut seen_variants = BTreeSet::new();
    let mut checked_arms = Vec::new();
    for (arm_index, arm) in arms.iter().enumerate() {
        if arm.type_name != parameter_value.algebraic_type.name {
            return Err(ClickError::new(format!(
                "structural induction pattern `{}::{}` does not match parameter type `{}`",
                arm.type_name, arm.variant, parameter_value.algebraic_type.name
            )));
        }
        if !seen_variants.insert(arm.variant.as_str()) {
            return Err(ClickError::new(format!(
                "duplicate structural induction arm `{}::{}`",
                arm.type_name, arm.variant
            )));
        }
        let Some(variant) = parameter_value
            .algebraic_type
            .variants
            .iter()
            .find(|candidate| candidate.name == arm.variant)
        else {
            return Err(ClickError::new(format!(
                "unknown structural induction variant `{}::{}`",
                arm.type_name, arm.variant
            )));
        };
        if arm.bindings.len() != variant.fields.len() {
            return Err(ClickError::new(format!(
                "pattern `{}::{}` expects {} binding(s), got {}",
                arm.type_name,
                arm.variant,
                variant.fields.len(),
                arm.bindings.len()
            )));
        }
        let mut distinct_bindings = BTreeSet::new();
        for binding in &arm.bindings {
            if !distinct_bindings.insert(binding.as_str()) {
                return Err(ClickError::new(format!(
                    "pattern `{}::{}` repeats binding `{binding}`",
                    arm.type_name, arm.variant
                )));
            }
            if theorem_parameter_names.contains(binding.as_str()) || binding == hypothesis {
                return Err(ClickError::new(format!(
                    "structural induction binding `{binding}` conflicts with a theorem parameter or the induction hypothesis"
                )));
            }
        }

        let mut branch_context = context.clone();
        let mut branch_algebraic_values = BTreeMap::new();
        let mut branch_bindings = BTreeMap::new();
        let mut constructor_arguments = Vec::new();
        for (field_index, (binding, field_type)) in
            arm.bindings.iter().zip(&variant.fields).enumerate()
        {
            let binding_expression = ContractExpression::Binding(binding.clone());
            constructor_arguments.push(binding_expression.clone());
            match field_type {
                AlgebraicValueType::C(c_type) => {
                    if matches!(
                        c_type,
                        CType::Void
                            | CType::Int16Array(_)
                            | CType::UInt16Array(_)
                            | CType::Int32Array(_)
                            | CType::UInt8Array(_)
                            | CType::UInt32Array(_)
                            | CType::Int64Array(_)
                            | CType::UInt64Array(_)
                            | CType::Float32Array(_)
                            | CType::Float64Array(_)
                    ) {
                        return Err(ClickError::new(
                            "structural induction does not support void or array-valued constructor fields",
                        ));
                    }
                    let variable = Variable(
                        STRUCTURAL_INDUCTION_VARIABLE_BASE
                            + (arm_index as u64) * 65_536
                            + field_index as u64,
                    );
                    branch_context.values.insert(
                        binding.clone(),
                        crate::kernel::symbolic_call_result(*c_type, variable),
                    );
                }
                algebraic @ (AlgebraicValueType::Algebraic { .. }
                | AlgebraicValueType::Parameter(_)) => {
                    let ClickType::Algebraic(algebraic_type) =
                        click_type_from_algebraic_value_type(algebraic)?
                    else {
                        unreachable!("algebraic field conversion preserves its family")
                    };
                    let symbolic = ContractExpression::AlgebraicVariable {
                        name: binding.clone(),
                        algebraic_type,
                        binder_index: theorem.parameters().len()
                            + 1
                            + arm_index * 256
                            + field_index,
                    };
                    let captured = capture_fixed_state_algebraic_expression(
                        &symbolic,
                        &PureFactContext::new(),
                        &branch_context.values,
                        &branch_context.array_refs,
                        &state,
                        &state,
                        None,
                        &RecordedSnapshots::new(),
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
                    branch_algebraic_values.insert(binding.clone(), captured);
                    branch_bindings.insert(binding.clone(), symbolic);
                }
                AlgebraicValueType::Integer => {
                    return Err(ClickError::new(
                        "structural induction over Integer-valued constructor fields is not yet supported",
                    ));
                }
            }
        }
        let constructor = ContractExpression::AlgebraicConstructor {
            algebraic_type: parameter_type.clone(),
            variant: arm.variant.clone(),
            arguments: constructor_arguments,
        };
        let case_substitution = BTreeMap::from([(parameter.clone(), constructor)]);
        let branch_surface_goal = substitute_click_proposition(surface_goal, &case_substitution)
            .map_err(ClickError::new)?;
        let branch_goal = lower_pure_theorem_proposition_with_algebraic_values(
            claim_label,
            &branch_surface_goal,
            &branch_context.values,
            &branch_context.array_refs,
            &branch_algebraic_values,
            &branch_context.memory,
            predicate_environment,
            click_function_environment,
        )
        .map_err(ClickError::new)?;
        let mut branch_surface_requires = Vec::new();
        let mut branch_requires = Vec::new();
        for requirement in theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
        {
            let surface = substitute_click_proposition(requirement, &case_substitution)
                .map_err(ClickError::new)?;
            let kernel = lower_pure_theorem_proposition_with_algebraic_values(
                claim_label,
                &surface,
                &branch_context.values,
                &branch_context.array_refs,
                &branch_algebraic_values,
                &branch_context.memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(ClickError::new)?;
            branch_surface_requires.push(surface);
            branch_requires.push(kernel);
        }
        let mut applications = Vec::new();
        for (binding, field_type) in arm.bindings.iter().zip(&variant.fields) {
            if field_type != &root_value_type {
                continue;
            }
            let argument = ContractExpression::Binding(binding.clone());
            let child_substitution = BTreeMap::from([(parameter.clone(), argument.clone())]);
            let mut surface_premises = Vec::new();
            let mut kernel_premises = Vec::new();
            for requirement in theorem
                .requires()
                .iter()
                .filter_map(Requirement::proposition)
            {
                let surface = substitute_click_proposition(requirement, &child_substitution)
                    .map_err(ClickError::new)?;
                let kernel = lower_pure_theorem_proposition_with_algebraic_values(
                    claim_label,
                    &surface,
                    &branch_context.values,
                    &branch_context.array_refs,
                    &branch_algebraic_values,
                    &branch_context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(ClickError::new)?;
                surface_premises.push(surface);
                kernel_premises.push(kernel);
            }
            let child_surface_goal =
                substitute_click_proposition(surface_goal, &child_substitution)
                    .map_err(ClickError::new)?;
            let conclusion = lower_pure_theorem_proposition_with_algebraic_values(
                claim_label,
                &child_surface_goal,
                &branch_context.values,
                &branch_context.array_refs,
                &branch_algebraic_values,
                &branch_context.memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(ClickError::new)?;
            let implication = kernel_premises
                .iter()
                .rev()
                .fold(conclusion.clone(), |body, premise| {
                    Proposition::Implies(Box::new(premise.clone()), Box::new(body))
                });
            branch_requires.push(implication.clone());
            applications.push(PureStructuralInductionApplication {
                argument,
                surface_premises,
                kernel_premises,
                implication,
                conclusion,
            });
        }
        branch_context.requires = branch_requires.clone();
        branch_context.surface_requirements = SurfacePropositionMap::default();
        for (surface, kernel) in branch_surface_requires.iter().zip(&branch_requires) {
            branch_context
                .surface_requirements
                .record_lowering(surface, kernel)?;
        }
        let branch_setup = PureStructuralInductionBranchSetup {
            hypothesis: hypothesis.clone(),
            applications,
            algebraic_values: branch_algebraic_values,
        };
        let prepared = prepare_structural_induction_arm_tactics(
            &arm.tactics,
            &branch_setup,
            &branch_bindings,
        )?;
        let root = Proof::for_pure_surface_goal_with_structural_induction(
            claim_label,
            &branch_requires,
            branch_goal,
            branch_surface_goal,
            &branch_context,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            branch_setup,
        );
        let Some(proof) = root.try_authoritative_linear_script(&prepared)? else {
            return Err(ClickError::new(format!(
                "`{claim_label}` structural induction arm `{}::{}` did not close its goal",
                arm.type_name, arm.variant
            )));
        };
        checked_arms.push(ProofInductionArm {
            type_name: arm.type_name.clone(),
            variant: arm.variant.clone(),
            bindings: arm.bindings.clone(),
            tactics: proof.completed_certificate()?.to_proof_tactics(),
        });
    }
    let missing = parameter_value
        .algebraic_type
        .variants
        .iter()
        .filter(|variant| !seen_variants.contains(variant.name.as_str()))
        .map(|variant| variant.name.as_str())
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        return Err(ClickError::new(format!(
            "structural induction is missing arm(s): {}",
            missing.join(", ")
        )));
    }
    ProofCertificate::from_proof_tactics(&[ProofTactic::StructuralInduct {
        parameter: parameter.clone(),
        hypothesis: hypothesis.clone(),
        arms: checked_arms,
    }])
    .map_err(|error| {
        ClickError::new(format!(
            "structural induction for `{claim_label}` produced an invalid certificate: {error:?}"
        ))
    })
}

pub(super) fn pure_theorem_context(
    theorem: &TheoremDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<PureTheoremContext, ClickError> {
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(theorem.parameters());
    let integer_values = pure_theorem_parameter_integer_values(theorem.parameters());
    let array_refs = pure_theorem_array_refs(theorem.parameters(), &values, &memory);
    let requires = theorem
        .requires()
        .iter()
        .map(|requirement| {
            let Some(proposition) = requirement.proposition() else {
                return Err(ClickError::new(format!(
                    "pure theorem `{}` currently supports proposition `requires` clauses only",
                    theorem.name()
                )));
            };
            lower_pure_theorem_proposition_with_integer_values(
                theorem.name(),
                proposition,
                &values,
                &integer_values,
                &array_refs,
                &memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "theorem `{}` setup failed: could not lower requirement: {message}",
                    theorem.name()
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut surface_requirements = SurfacePropositionMap::default();
    for (kernel, surface) in requires.iter().zip(
        theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition),
    ) {
        surface_requirements.record_lowering(surface, kernel)?;
    }
    Ok(PureTheoremContext {
        memory,
        values,
        integer_values,
        array_refs,
        requires,
        surface_requirements,
    })
}

fn pure_theorem_parameter_integer_values(
    parameters: &[FunctionParameter],
) -> crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression> {
    parameters
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.click_type(), ClickType::Integer))
        .fold(
            crate::persistent::PersistentMap::default(),
            |values, (index, parameter)| {
                values.with_inserted(
                    parameter.name().to_string(),
                    crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(
                        crate::kernel::Variable(index as u64),
                    )),
                )
            },
        )
}

pub(in crate::surface) fn pure_theorem_parameter_values(
    parameters: &[FunctionParameter],
) -> BTreeMap<String, CValue> {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            let c_type = parameter.click_type().c_type()?;
            let value = match c_type {
                C0Type::Void => unreachable!("pure theorem parameters cannot be void"),
                C0Type::Bool => {
                    crate::kernel::bool_value(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::VoidPointer => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            1,
                        ),
                    },
                    CType::VoidPointer,
                ),
                C0Type::Int16 => CValue::Int16(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int32 => CValue::Int32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt32 => CValue::UInt32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Char => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt8 => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt16 => CValue::UInt16(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int64 => CValue::Int64(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt64 => CValue::UInt64(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Float32 => {
                    CValue::Float32(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::Float64 => {
                    CValue::Float64(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::Int16Pointer | C0Type::Int16Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            2,
                        ),
                    },
                    CType::Int16Pointer,
                ),
                C0Type::UInt16Pointer | C0Type::UInt16Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            2,
                        ),
                    },
                    CType::UInt16Pointer,
                ),
                C0Type::Int32Pointer | C0Type::Int32Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            4,
                        ),
                    },
                    CType::Int32Pointer,
                ),
                C0Type::CharPointer
                | C0Type::CharArray(_)
                | C0Type::UInt8Pointer
                | C0Type::UInt8Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            1,
                        ),
                    },
                    CType::UInt8Pointer,
                ),
                C0Type::UInt32Pointer | C0Type::UInt32Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            4,
                        ),
                    },
                    CType::UInt32Pointer,
                ),
                C0Type::Int64Pointer | C0Type::Int64Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            8,
                        ),
                    },
                    CType::Int64Pointer,
                ),
                C0Type::UInt64Pointer | C0Type::UInt64Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            8,
                        ),
                    },
                    CType::UInt64Pointer,
                ),
                C0Type::Float32Pointer | C0Type::Float32Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            4,
                        ),
                    },
                    CType::Float32Pointer,
                ),
                C0Type::Float64Pointer | C0Type::Float64Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            8,
                        ),
                    },
                    CType::Float64Pointer,
                ),
                C0Type::Int32PointerPointer
                | C0Type::CharPointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int64PointerPointer
                | C0Type::UInt64PointerPointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer => {
                    let element_width = c_type
                        .pointee_type()
                        .expect("pointer-to-pointer parameter has a pointee")
                        .to_kernel_type()
                        .byte_width();
                    CValue::typed_pointer(
                        Pointer {
                            block: PointerBlock::ExternalArgument,
                            offset: scale_int32_offset(
                                Bitvector32Term::Variable(Variable(
                                    POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                                )),
                                i64::from(element_width),
                            ),
                        },
                        c_type.to_kernel_type(),
                    )
                }
                C0Type::FunctionPointer(_) => CValue::typed_pointer(
                    Pointer::symbolic_function(Variable(index as u64)),
                    c_type.to_kernel_type(),
                ),
            };
            Some((parameter.name().to_string(), value))
        })
        .collect()
}

pub(in crate::surface) fn pure_theorem_array_refs(
    parameters: &[FunctionParameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let c_type = parameter.click_type().c_type()?;
            let element_type = click_array_element_type(c_type)?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.pointer().clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

fn theorem_claim_label(
    theorem_name: &str,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
) -> String {
    match ensure_clause.name() {
        Some(name) => format!("{theorem_name}.{name}"),
        None => format!("{theorem_name}.ensures_{ensure_index}"),
    }
}

fn lower_pure_simp_certificate(
    theorem: &TheoremDefinition,
    context: &PureTheoremContext,
    goal: &Proposition,
    surface_goal: &ClickProposition,
    certificate: &SimpEvidence,
) -> Option<Vec<ProofTactic>> {
    let tactic = match certificate {
        SimpEvidence::Assumption => ProofTactic::Assumption,
        SimpEvidence::Normalize => {
            let tactics = plan_context_free_normalization(goal, surface_goal)?;
            ProofCertificate::from_proof_tactics(&tactics).ok()?;
            return Some(tactics);
        }
        SimpEvidence::Derivation(derivation) => {
            if derivation
                .algebraic_constructor_injectivity_source()
                .is_some()
            {
                let tactic = ProofTactic::Extract(surface_goal.clone());
                ProofCertificate::from_proof_tactics(std::slice::from_ref(&tactic)).ok()?;
                return Some(vec![tactic]);
            }
            let premise_pairs = derivation
                .context_premises()
                .iter()
                .map(|premise| {
                    context
                        .requires
                        .iter()
                        .position(|available| available == premise)
                        .and_then(|index| theorem.requires().get(index))
                        .and_then(Requirement::proposition)
                        .cloned()
                        .map(|surface| (premise.clone(), surface))
                })
                .collect::<Option<Vec<_>>>()?;
            if let Some((_, surface)) = premise_pairs.iter().find(|(kernel, _)| {
                normalizes_context_free(&Proposition::Not(Box::new(kernel.clone())))
            }) {
                let tactic = ProofTactic::Contradiction(surface.clone());
                ProofCertificate::from_proof_tactics(std::slice::from_ref(&tactic)).ok()?;
                return Some(vec![tactic]);
            }
            if premise_pairs.is_empty() {
                let tactics = plan_context_free_normalization(goal, surface_goal)?;
                ProofCertificate::from_proof_tactics(&tactics).ok()?;
                return Some(tactics);
            } else if let Some(ordered) = recorded_signed_order_pairs(derivation, &premise_pairs)
                && let Some(tactics) = plan_recorded_signed_order_path(goal, &ordered)
            {
                return Some(tactics);
            } else if let Some(tactics) =
                plan_recorded_bitvector_equality_path(goal, derivation, &premise_pairs)
            {
                return Some(tactics);
            } else if let Ok(tactics) =
                lower_restricted_simp_plan(goal, None, certificate, &premise_pairs)
            {
                return Some(tactics);
            } else {
                return None;
            }
        }
    };
    ProofCertificate::from_proof_tactics(std::slice::from_ref(&tactic)).ok()?;
    Some(vec![tactic])
}

fn verify_theorem_ensure(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<VerifiedPureTheorem, ClickError> {
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(format!(
            "pure theorem `{}` currently supports proposition `ensures` clauses only",
            theorem.name()
        )));
    };
    if let Some(verified) = verify_contract_refinement_theorem(
        theorem,
        ensure_index,
        ensure_clause,
        claim_label,
        surface_goal,
        context,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        function_environment,
    )? {
        return Ok(verified);
    }
    let lowering_assumptions = assumptions_from_propositions(&context.requires);
    let (goal, goal_introductions) = lower_pure_theorem_proposition_recording_introductions(
        theorem.name(),
        surface_goal,
        &lowering_assumptions,
        &context.values,
        &context.array_refs,
        &BTreeMap::new(),
        &context.integer_values,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` failed: could not lower conclusion: {message}"
        ))
    })?;

    if is_kernel_standard_theorem_name(theorem.name()) {
        return verify_kernel_standard_theorem_axiom(
            theorem,
            ensure_index,
            ensure_clause,
            claim_label,
            context,
            goal,
        );
    }

    let checked_certificate;
    let mut legacy_induction_diagnostic = None;
    let (proof_kind, source_tactics, induction_setup) = match ensure_clause.proof() {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto) => {
            checked_certificate = check_direct_pure_goal_with_proof(
                claim_label,
                context,
                surface_goal,
                &goal,
                &goal_introductions,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            )?
            .map(|(certificate, completion)| (certificate, Some(completion)));
            if checked_certificate.is_none() {
                prove_pure_theorem_goal(
                    claim_label,
                    "auto",
                    &context.requires,
                    &goal,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    context,
                    &[],
                    &[],
                    true,
                )?;
            }
            (ProofKind::Pure, None, None)
        }
        SourceProof::Tactic(SmartTactic::Simp) => {
            checked_certificate = check_direct_pure_goal_with_proof(
                claim_label,
                context,
                surface_goal,
                &goal,
                &goal_introductions,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            )?
            .map(|(certificate, completion)| (certificate, Some(completion)));
            if checked_certificate.is_none() {
                prove_pure_theorem_goal(
                    claim_label,
                    "simp",
                    &context.requires,
                    &goal,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    context,
                    &[],
                    &[],
                    true,
                )?;
            }
            (ProofKind::Simp, None, None)
        }
        SourceProof::Script(tactics) => {
            if tactics.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` has an empty explicit proof script"
                )));
            }
            if matches!(tactics.first(), Some(ProofTactic::StructuralInduct { .. })) {
                // Structural induction binds an algebraic parameter, which is
                // outside the int32 binder shape kernel authority accepts, so
                // no completion is retained for it.
                checked_certificate = Some((
                    check_pure_structural_induction(
                        theorem,
                        claim_label,
                        context,
                        surface_goal,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                        tactics,
                    )?,
                    None,
                ));
                (ProofKind::TacticScript, None, None)
            } else {
                let (tactics, induction_setup) =
                    prepare_pure_induction_tactics(theorem, surface_goal, tactics)?;
                checked_certificate = if induction_setup.is_none() {
                    check_pure_script_with_proof(
                        claim_label,
                        context,
                        surface_goal,
                        &goal,
                        &goal_introductions,
                        &tactics,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                    )?
                    .map(|(certificate, completion)| (certificate, Some(completion)))
                } else {
                    None
                };
                if checked_certificate.is_some() {
                    (ProofKind::TacticScript, None, induction_setup)
                } else {
                    // Keep the old walk only as a diagnostic fallback for
                    // rejected source shapes. Its success is ignored, and its
                    // failure is consulted only if the checked gateway also
                    // rejects the generated certificate.
                    let legacy_result = prove_pure_theorem_script(
                        claim_label,
                        &context.requires,
                        &goal,
                        Some(surface_goal),
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                        context,
                        &tactics,
                        induction_setup.as_ref(),
                    );
                    if induction_setup.is_some() {
                        legacy_induction_diagnostic = legacy_result.err();
                    } else {
                        legacy_result?;
                    }
                    (ProofKind::TacticScript, Some(tactics), induction_setup)
                }
            }
        }
    };

    let (certificate, checked_completion) = match checked_certificate {
        Some(checked) => checked,
        None => {
            let gateway = pure_goal_proof_certificate_gateway(
                claim_label,
                || {
                    pure_theorem_surface_certificate(
                        theorem,
                        claim_label,
                        context,
                        &goal,
                        surface_goal,
                        source_tactics.as_deref(),
                        predicate_environment,
                        click_function_environment,
                        induction_setup.as_ref(),
                    )
                },
                |certificate| {
                    validate_pure_theorem_certificate(
                        claim_label,
                        &context.requires,
                        &goal,
                        predicate_environment,
                        click_function_environment,
                        theorem_environment,
                        context,
                        certificate,
                        induction_setup.as_ref(),
                    )
                },
            );
            match gateway {
                Ok(result) => result,
                Err(error) => match legacy_induction_diagnostic {
                    Some(diagnostic) => return Err(diagnostic),
                    None => return Err(error),
                },
            }
        }
    };
    let kernel_variables = theorem
        .parameters()
        .iter()
        .map(|parameter| match context.values.get(parameter.name()) {
            Some(CValue::Int32(Bitvector32Term::Variable(variable))) => Some(*variable),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    // Kernel authority now comes from the completion the checked proof already
    // issued, never from a second proof of the same conclusion. A certificate
    // whose only steps are cited rewrites and a normalizing closer offers that
    // rewrite chain to the kernel as well, so the retained certificate's own
    // citations are validated; the plain constructor remains the route for
    // every other shape, and for a rewrite chain the kernel rejects.
    let kernel_authority = match (kernel_variables, checked_completion) {
        (Some(variables), Some(completion)) => certificate_int32_rewrites(
            &certificate,
            claim_label,
            context,
            predicate_environment,
            click_function_environment,
        )
        .and_then(|rewrites| {
            prove_universally_quantified_pure_implication_by_int32_rewrites(
                context.requires.clone(),
                goal.clone(),
                variables.clone(),
                rewrites,
                &completion,
            )
        })
        .or_else(|| {
            prove_universally_quantified_pure_implication(
                context.requires.clone(),
                goal.clone(),
                variables,
                &completion,
            )
        }),
        _ => None,
    };
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind,
        proof: Some(certificate),
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority,
    })
}

#[allow(clippy::too_many_arguments)]
fn verify_contract_refinement_theorem(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    surface_goal: &ClickProposition,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<Option<VerifiedPureTheorem>, ClickError> {
    let ClickProposition::PredicateCall { name, arguments } = surface_goal else {
        return Ok(None);
    };
    let Some(contract_definition) = predicate_environment.contract_definition(name) else {
        return Ok(None);
    };
    let [argument] = arguments.as_slice() else {
        return Ok(None);
    };
    let concrete_target = contract_expression_function_address(argument);
    let symbolic_binding = match argument {
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => Some(name.as_str()),
        _ => None,
    };
    if concrete_target.is_none() && symbolic_binding.is_none() {
        return Ok(None);
    }
    let source_contract = if concrete_target.is_some() {
        if !theorem.parameters().is_empty() || !theorem.requires().is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}`: refinement of a concrete function must be closed and have no `requires` clauses"
            )));
        }
        None
    } else {
        let binding = symbolic_binding.expect("non-concrete refinement has a symbolic binding");
        let [parameter] = theorem.parameters() else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: abstract contract refinement requires exactly one function-pointer theorem parameter"
            )));
        };
        if parameter.name() != binding || !matches!(parameter.c_type(), C0Type::FunctionPointer(_))
        {
            return Err(ClickError::new(format!(
                "`{claim_label}`: `{binding}` must be the theorem's function-pointer parameter"
            )));
        }
        let [requirement] = theorem.requires() else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: abstract contract refinement requires exactly one source-contract fact"
            )));
        };
        let Some(ClickProposition::PredicateCall {
            name: source_name,
            arguments: source_arguments,
        }) = requirement.proposition()
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: abstract contract refinement requires a source-contract proposition"
            )));
        };
        let [source_argument] = source_arguments.as_slice() else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: source contract `{source_name}` expects the symbolic callback argument"
            )));
        };
        if source_argument != argument {
            return Err(ClickError::new(format!(
                "`{claim_label}`: source and target contracts must describe the same symbolic callback `{binding}`"
            )));
        }
        let source_definition = predicate_environment
            .contract_definition(source_name)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}`: `{source_name}` is not a named function contract"
                ))
            })?;
        Some((source_name.as_str(), source_definition))
    };
    let SourceProof::Script(tactics) = ensure_clause.proof() else {
        let subject = concrete_target
            .map(|target| format!("&{target}"))
            .or_else(|| symbolic_binding.map(str::to_string))
            .expect("a refinement theorem has a recognized subject");
        return Err(ClickError::new(format!(
            "`{claim_label}`: proving `{name}({subject})` requires an explicit contract-refinement proof"
        )));
    };
    let proof_tactics = if let Some((source_name, _)) = source_contract {
        let Some((first_two, remainder)) = tactics.split_at_checked(2) else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: abstract refinement must begin by unfolding `{source_name}` and `{name}`"
            )));
        };
        let unfolded = first_two
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::UnfoldPredicate(unfolded) => Some(unfolded.as_str()),
                _ => None,
            })
            .collect::<Option<BTreeSet<_>>>();
        let expected = BTreeSet::from([source_name, name.as_str()]);
        if unfolded.as_ref() != Some(&expected) {
            return Err(ClickError::new(format!(
                "`{claim_label}`: abstract refinement must begin by unfolding `{source_name}` and `{name}`"
            )));
        }
        remainder
    } else {
        let Some((ProofTactic::UnfoldPredicate(unfolded), remainder)) = tactics.split_first()
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: contract-refinement proof must begin with `unfold({name});`"
            )));
        };
        if unfolded != name {
            return Err(ClickError::new(format!(
                "`{claim_label}`: expected `unfold({name});`, got `unfold({unfolded});`"
            )));
        }
        remainder
    };
    let function_environment = function_environment.ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}`: contract-refinement theorems require the C function environment"
        ))
    })?;
    let refinement = match (concrete_target, source_contract) {
        (Some(target), None) => {
            c_function_contract_refinement_context(function_environment, name, target).ok_or_else(
                || {
                    ClickError::new(format!(
                        "`{claim_label}`: `{target}` is not a verified or external function compatible with contract `{name}`"
                    ))
                },
            )?
        }
        (None, Some((source_name, _))) => {
            let binding = symbolic_binding.expect("abstract refinement has a callback binding");
            let pointer = context.values.get(binding).ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}`: symbolic callback `{binding}` has no theorem value"
                ))
            })?;
            c_contract_refinement_context(function_environment, name, source_name, pointer)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}`: contract `{source_name}` is not signature-compatible with `{name}`"
                    ))
                })?
        }
        _ => unreachable!("refinement subject classification is exhaustive"),
    };
    let argument_values = c_function_contract_refinement_arguments(&refinement);
    let contract_parameters = contract_definition
        .function_block()
        .signature()
        .parameters();
    if contract_parameters.len() != argument_values.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}`: contract parameter count does not match its lowered function"
        )));
    }
    let refinement_failure = || {
        let subject = concrete_target
            .map(|target| format!("&{target}"))
            .or_else(|| symbolic_binding.map(str::to_string))
            .expect("refinement subject");
        ClickError::new(format!(
            "`{claim_label}`: contract-refinement proof does not establish `{name}({subject})`"
        ))
    };
    let obligations =
        c_function_contract_refinement_obligations(&refinement).ok_or_else(refinement_failure)?;
    let arguments = argument_values
        .iter()
        .cloned()
        .map(CExpression::Value)
        .collect::<Vec<_>>();
    let parameters = contract_parameters
        .iter()
        .map(|parameter| {
            syntax::C0Parameter::new(
                parameter.c_type(),
                parameter.name().to_string(),
                parameter.struct_name().map(str::to_string),
            )
        })
        .collect::<Vec<_>>();
    let proof_goal = obligations.proposition().clone();
    let presentation = super::surface_synthesis::synthesize_surface_proposition_at_entry_and_post(
        &proof_goal,
        &parameters,
        &arguments,
        obligations.entry(),
        obligations.post(),
    )
    .ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}`: cannot present contract-refinement obligations"
        ))
    })?;
    let snapshots = RecordedSnapshots::new();
    let mut surfaces = SurfacePropositionMap::default();
    let mut pending = vec![(&proof_goal, &presentation)];
    while let Some((kernel, surface)) = pending.pop() {
        match (kernel, surface) {
            (Proposition::And(kl, kr), ClickProposition::And(sl, sr))
            | (Proposition::Or(kl, kr), ClickProposition::Or(sl, sr))
            | (Proposition::Implies(kl, kr), ClickProposition::Implies(sl, sr)) => {
                pending.push((kl, sl));
                pending.push((kr, sr));
            }
            (Proposition::Not(k), ClickProposition::Not(s)) => pending.push((k, s)),
            _ => surfaces.record_lowering(surface, kernel)?,
        }
    }
    let root = Proof::for_contract_refinement_goal(
        claim_label,
        proof_goal,
        presentation,
        &parameters,
        &arguments,
        obligations.entry(),
        obligations.post(),
        &snapshots,
        &surfaces,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    );
    let proof = root
        .try_authoritative_linear_script(proof_tactics)?
        .ok_or_else(refinement_failure)?;
    let checked = proof.completed_proposition()?;
    let goal = lower_pure_theorem_proposition_with_integer_values(
        theorem.name(),
        surface_goal,
        &context.values,
        &context.integer_values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` failed: could not lower conclusion: {message}"
        ))
    })?;
    let kernel_authority = prove_c_function_contract_refinement(
        &refinement,
        goal.clone(),
        &checked,
    )
    .ok_or_else(|| {
        let subject = concrete_target
            .map(|target| format!("&{target}"))
            .or_else(|| symbolic_binding.map(str::to_string))
            .expect("refinement theorem has a subject");
        ClickError::new(format!(
            "`{claim_label}`: contract-refinement proof does not establish `{name}({subject})`"
        ))
    })?;
    let mut certificate_steps =
        ProofCertificate::from_proof_tactics(&tactics[..tactics.len() - proof_tactics.len()])
            .map_err(|error| ClickError::new(format!("{error:?}")))?
            .steps()
            .to_vec();
    certificate_steps.extend_from_slice(proof.completed_certificate()?.steps());
    let certificate = ProofCertificate::from_steps(certificate_steps)?;
    Ok(Some(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind: ProofKind::TacticScript,
        proof: Some(certificate),
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority: Some(kernel_authority),
    }))
}

/// Lets direct smart pure proofs search by applying checked proof steps.
///
/// Failed descendants are simply discarded. A successful descendant already
/// owns both the semantic successor and the exact simple certificate that
/// produced it, so ordinary operation does not reconstruct and check that
/// certificate through the legacy gateway.
#[allow(clippy::too_many_arguments)]
/// The ordered int32 equalities a `rewrite ...; normalize` certificate cites.
///
/// Returns `None` for any other certificate shape, or when a cited surface
/// proposition does not lower.
fn certificate_int32_rewrites(
    certificate: &ProofCertificate,
    claim_label: &str,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Option<Vec<Proposition>> {
    let steps = certificate.steps();
    let (rewrite_steps, closer) = steps.split_at(steps.len().saturating_sub(1));
    if !matches!(closer, [ProofStep::Normalize]) || rewrite_steps.is_empty() {
        return None;
    }
    rewrite_steps
        .iter()
        .map(|step| match step {
            ProofStep::Rewrite(surface) => lower_pure_theorem_proposition(
                claim_label,
                surface,
                &context.values,
                &context.array_refs,
                &context.memory,
                predicate_environment,
                click_function_environment,
            )
            .ok(),
            _ => None,
        })
        .collect()
}

fn check_direct_pure_goal_with_proof(
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    goal_introductions: &crate::kernel::LoweringIntroductions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Option<(ProofCertificate, crate::kernel::proof::CheckedProposition)>, ClickError> {
    let root = Proof::for_pure_surface_goal(
        claim_label,
        &context.requires,
        goal.clone(),
        surface_goal.clone(),
        context,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    )
    .with_recorded_goal_introductions(Some(goal_introductions.clone()));
    let Some(proof) = root.try_simp_closure()? else {
        return Ok(None);
    };
    Ok(Some((
        proof.completed_certificate()?,
        proof.completed_proposition()?,
    )))
}

/// Names whose declarations are checked directly against kernel arithmetic axioms.
fn integer_round_trip_destination(name: &str) -> Option<crate::kernel::MachineIntegerType> {
    use crate::kernel::MachineIntegerType;
    Some(match name {
        "integer_to_int16_round_trip" => MachineIntegerType::Int16,
        "integer_to_int32_round_trip" => MachineIntegerType::Int32,
        "integer_to_uint8_round_trip" => MachineIntegerType::UInt8,
        "integer_to_uint16_round_trip" => MachineIntegerType::UInt16,
        "integer_to_uint32_round_trip" => MachineIntegerType::UInt32,
        "integer_to_int64_round_trip" => MachineIntegerType::Int64,
        "integer_to_uint64_round_trip" => MachineIntegerType::UInt64,
        _ => return None,
    })
}

pub(in crate::surface) fn is_kernel_standard_theorem_name(name: &str) -> bool {
    integer_round_trip_destination(name).is_some()
        || matches!(
            name,
            "int32_add_defined_by_integer_bounds"
                | "int32_add_to_integer"
                | "int32_subtract_to_integer"
                | "int32_increment_upper_bound"
                | "int32_increment_strictly_increases"
                | "int32_increment_lower_bound"
                | "int32_increment_greater_equal_lower_bound"
                | "int32_increment_strict_greater_lower_bound"
                | "int32_increment_preserves_order"
                | "int32_le_lt_transitive"
                | "int32_le_transitive"
                | "int32_lt_le_transitive"
                | "int32_lt_transitive"
                | "int32_ge_transitive"
                | "int32_ge_implies_reversed_le"
                | "int32_le_implies_reversed_ge"
                | "int32_le_and_not_lt_implies_eq"
                | "int32_le_and_neq_implies_lt"
                | "int32_ge_and_not_gt_implies_eq"
                | "int32_le_antisymmetric"
                | "int32_positive_is_nonnegative"
                | "int32_lt_implies_le"
                | "int32_lt_implies_neq"
                | "int32_not_lt_implies_ge"
                | "int32_strictly_positive_is_nonnegative"
                | "int32_increment_below_max_is_defined"
                | "int32_one_plus_below_max_is_defined"
                | "int32_one_plus_strictly_increases"
                | "int32_nonnegative_add_within_max_is_defined"
                | "int32_nonnegative_subtract_within_value_is_defined"
                | "int32_move_one_from_right_to_left_preserves_sum"
                | "int32_add_nonnegative_right_is_at_least_left"
                | "int32_add_nonnegative_left_is_at_least_right"
                | "int32_above_one_predecessor_is_at_least_one"
                | "int32_positive_predecessor_is_nonnegative"
                | "int32_positive_predecessor_strictly_decreases"
                | "int32_nonnegative_predecessor_upper_bound"
                | "int32_successor_le_implies_lt"
                | "int32_lt_successor_implies_le"
        )
}

fn verify_kernel_standard_theorem_axiom(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: Proposition,
) -> Result<VerifiedPureTheorem, ClickError> {
    let (parameter_count, requirement_count) = match theorem.name() {
        name if integer_round_trip_destination(name).is_some() => (1, 2),
        "int32_add_defined_by_integer_bounds" => (2, 2),
        "int32_add_to_integer" | "int32_subtract_to_integer" => (2, 1),
        "int32_increment_upper_bound" | "int32_increment_strictly_increases" => (2, 1),
        "int32_increment_lower_bound"
        | "int32_increment_greater_equal_lower_bound"
        | "int32_increment_strict_greater_lower_bound"
        | "int32_increment_preserves_order" => (3, 2),
        "int32_successor_le_implies_lt" => (2, 2),
        "int32_lt_successor_implies_le" => (2, 1),
        "int32_nonnegative_predecessor_upper_bound"
        | "int32_nonnegative_add_within_max_is_defined"
        | "int32_nonnegative_subtract_within_value_is_defined"
        | "int32_add_nonnegative_right_is_at_least_left"
        | "int32_add_nonnegative_left_is_at_least_right" => (2, 2),
        "int32_move_one_from_right_to_left_preserves_sum" => (3, 3),
        "int32_le_antisymmetric" => (2, 2),
        "int32_le_and_not_lt_implies_eq"
        | "int32_le_and_neq_implies_lt"
        | "int32_ge_and_not_gt_implies_eq" => (2, 2),
        "int32_ge_implies_reversed_le" => (2, 1),
        "int32_le_implies_reversed_ge" => (2, 1),
        "int32_lt_implies_le" | "int32_lt_implies_neq" | "int32_not_lt_implies_ge" => (2, 1),
        "int32_positive_is_nonnegative"
        | "int32_strictly_positive_is_nonnegative"
        | "int32_increment_below_max_is_defined"
        | "int32_one_plus_below_max_is_defined"
        | "int32_one_plus_strictly_increases"
        | "int32_above_one_predecessor_is_at_least_one"
        | "int32_positive_predecessor_is_nonnegative"
        | "int32_positive_predecessor_strictly_decreases" => (1, 1),
        "int32_le_lt_transitive"
        | "int32_le_transitive"
        | "int32_lt_le_transitive"
        | "int32_lt_transitive"
        | "int32_ge_transitive" => (3, 2),
        _ => unreachable!("only registered kernel standard theorems call this verifier"),
    };
    if ensure_index != 0
        || theorem.parameters().len() != parameter_count
        || theorem.requires().len() != requirement_count
        || theorem.ensures().len() != 1
        || !matches!(ensure_clause.proof(), SourceProof::Default)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` does not have the declaration shape required by its kernel axiom",
        )));
    }
    let axiom = if let Some(destination) = integer_round_trip_destination(theorem.name()) {
        let parameter = &theorem.parameters()[0];
        let Some(crate::kernel::SpecIntegerExpression::Term(value)) =
            context.integer_values.get(parameter.name())
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}` kernel parameter must be Integer"
            )));
        };
        crate::kernel::prove_integer_machine_round_trip(value.clone(), destination)
    } else {
        let int32_parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(CValue::Int32(term)) => Ok(term.clone()),
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be int32",
                    parameter.name()
                ))),
            }
        };
        let value = int32_parameter(0)?;
        match theorem.name() {
            "int32_add_defined_by_integer_bounds" => {
                crate::kernel::prove_int32_add_defined_by_integer_bounds(value, int32_parameter(1)?)
            }
            "int32_add_to_integer" => {
                crate::kernel::prove_int32_add_to_integer(value, int32_parameter(1)?)
            }
            "int32_subtract_to_integer" => {
                crate::kernel::prove_int32_subtract_to_integer(value, int32_parameter(1)?)
            }
            "int32_increment_upper_bound" => {
                prove_int32_increment_upper_bound(value, int32_parameter(1)?)
            }
            "int32_increment_strictly_increases" => {
                prove_int32_increment_strictly_increases(value, int32_parameter(1)?)
            }
            "int32_increment_lower_bound" => {
                prove_int32_increment_lower_bound(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_increment_greater_equal_lower_bound" => {
                prove_int32_increment_greater_equal_lower_bound(
                    value,
                    int32_parameter(1)?,
                    int32_parameter(2)?,
                )
            }
            "int32_increment_strict_greater_lower_bound" => {
                prove_int32_increment_strict_greater_lower_bound(
                    value,
                    int32_parameter(1)?,
                    int32_parameter(2)?,
                )
            }
            "int32_increment_preserves_order" => prove_int32_increment_preserves_order(
                value,
                int32_parameter(1)?,
                int32_parameter(2)?,
            ),
            "int32_successor_le_implies_lt" => {
                prove_int32_successor_le_implies_lt(value, int32_parameter(1)?)
            }
            "int32_lt_successor_implies_le" => {
                prove_int32_lt_successor_implies_le(value, int32_parameter(1)?)
            }
            "int32_le_antisymmetric" => prove_int32_le_antisymmetric(value, int32_parameter(1)?),
            "int32_le_and_not_lt_implies_eq" => {
                prove_int32_le_and_not_lt_implies_eq(value, int32_parameter(1)?)
            }
            "int32_le_and_neq_implies_lt" => {
                prove_int32_le_and_neq_implies_lt(value, int32_parameter(1)?)
            }
            "int32_ge_and_not_gt_implies_eq" => {
                prove_int32_ge_and_not_gt_implies_eq(value, int32_parameter(1)?)
            }
            "int32_positive_is_nonnegative" => prove_int32_positive_is_nonnegative(value),
            "int32_lt_implies_le" => prove_int32_lt_implies_le(value, int32_parameter(1)?),
            "int32_lt_implies_neq" => prove_int32_lt_implies_neq(value, int32_parameter(1)?),
            "int32_not_lt_implies_ge" => prove_int32_not_lt_implies_ge(value, int32_parameter(1)?),
            "int32_strictly_positive_is_nonnegative" => {
                prove_int32_strictly_positive_is_nonnegative(value)
            }
            "int32_increment_below_max_is_defined" => {
                prove_int32_increment_below_max_is_defined(value)
            }
            "int32_one_plus_below_max_is_defined" => {
                prove_int32_one_plus_below_max_is_defined(value)
            }
            "int32_one_plus_strictly_increases" => prove_int32_one_plus_strictly_increases(value),
            "int32_nonnegative_add_within_max_is_defined" => {
                prove_int32_nonnegative_add_within_max_is_defined(value, int32_parameter(1)?)
            }
            "int32_nonnegative_subtract_within_value_is_defined" => {
                prove_int32_nonnegative_subtract_within_value_is_defined(value, int32_parameter(1)?)
            }
            "int32_move_one_from_right_to_left_preserves_sum" => {
                prove_int32_move_one_from_right_to_left_preserves_sum(
                    value.clone(),
                    int32_parameter(1)?,
                    int32_parameter(2)?,
                )
            }
            "int32_add_nonnegative_right_is_at_least_left" => {
                prove_int32_add_nonnegative_right_is_at_least_left(value, int32_parameter(1)?)
            }
            "int32_add_nonnegative_left_is_at_least_right" => {
                prove_int32_add_nonnegative_left_is_at_least_right(value, int32_parameter(1)?)
            }
            "int32_above_one_predecessor_is_at_least_one" => {
                prove_int32_above_one_predecessor_is_at_least_one(value)
            }
            "int32_positive_predecessor_is_nonnegative" => {
                prove_int32_positive_predecessor_is_nonnegative(value)
            }
            "int32_positive_predecessor_strictly_decreases" => {
                prove_int32_positive_predecessor_strictly_decreases(value)
            }
            "int32_nonnegative_predecessor_upper_bound" => {
                prove_int32_nonnegative_predecessor_upper_bound(value, int32_parameter(1)?)
            }
            "int32_le_lt_transitive" => {
                prove_int32_le_lt_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_le_transitive" => {
                prove_int32_le_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_lt_le_transitive" => {
                prove_int32_lt_le_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_lt_transitive" => {
                prove_int32_lt_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_ge_transitive" => {
                prove_int32_ge_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_ge_implies_reversed_le" => {
                prove_int32_ge_implies_reversed_le(value, int32_parameter(1)?)
            }
            "int32_le_implies_reversed_ge" => {
                prove_int32_le_implies_reversed_ge(value, int32_parameter(1)?)
            }
            _ => unreachable!("checked above"),
        }
    };
    let expected = context
        .requires
        .iter()
        .rev()
        .fold(goal.clone(), |body, requirement| {
            Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
        });
    if axiom.proposition() != &expected {
        return Err(ClickError::new(format!(
            "`{claim_label}` declaration does not match its kernel axiom",
        )));
    }
    let kernel_authority = match theorem.name() {
        "int32_above_one_predecessor_is_at_least_one" => {
            Some(certify_int32_above_one_predecessor_is_at_least_one())
        }
        "int32_move_one_from_right_to_left_preserves_sum" => {
            Some(certify_int32_move_one_from_right_to_left_preserves_sum())
        }
        _ => None,
    };
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind: ProofKind::Axiom,
        proof: None,
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority,
    })
}

/// Checks the pure-script subset already supported by the proof object.
///
/// Fully explicit proposition scripts advance directly through
/// `Proof::apply_step`. Linear scripts may interleave those checked steps with
/// bare theorem application and a final `simp`; both smart operations select
/// proof steps against the current `Proof`. Explicit `cases` certificates use
/// the audited branch/open/join operations recursively.
fn proof_supports_pure_certificate(certificate: &ProofCertificate) -> bool {
    certificate.steps().iter().all(|step| match step {
        ProofStep::ApplyTheoremUsing { .. }
        | ProofStep::UnfoldPredicate(_)
        | ProofStep::UnfoldFunction(_)
        | ProofStep::Assumption
        | ProofStep::Normalize
        | ProofStep::NormalizeUsing(_)
        | ProofStep::ArithmeticUsing(_)
        | ProofStep::IntegerCertificate(_)
        | ProofStep::Intro
        | ProofStep::Witness(_)
        | ProofStep::Choose(_)
        | ProofStep::Induct { .. }
        | ProofStep::ApplyInduction { .. }
        | ProofStep::Split
        | ProofStep::Left
        | ProofStep::Right
        | ProofStep::Enumerate
        | ProofStep::Rewrite(_)
        | ProofStep::Extract(_)
        | ProofStep::Contradiction(_) => true,
        ProofStep::Both {
            left_proof,
            right_proof,
        } => {
            proof_supports_pure_certificate(left_proof)
                && proof_supports_pure_certificate(right_proof)
        }
        ProofStep::Cases {
            left_proof,
            right_proof,
            ..
        } => {
            proof_supports_pure_certificate(left_proof)
                && proof_supports_pure_certificate(right_proof)
        }
        ProofStep::If {
            then_proof,
            else_proof,
            ..
        } => {
            proof_supports_pure_certificate(then_proof)
                && proof_supports_pure_certificate(else_proof)
        }
        ProofStep::Have { proof, .. } => proof_supports_pure_certificate(proof),
        _ => false,
    })
}

#[allow(clippy::too_many_arguments)]
fn check_pure_script_with_proof(
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    goal_introductions: &crate::kernel::LoweringIntroductions,
    tactics: &[ProofTactic],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Option<(ProofCertificate, crate::kernel::proof::CheckedProposition)>, ClickError> {
    let root = Proof::for_pure_surface_goal(
        claim_label,
        &context.requires,
        goal.clone(),
        surface_goal.clone(),
        context,
        predicate_environment,
        click_function_environment,
        theorem_environment,
    )
    .with_recorded_goal_introductions(Some(goal_introductions.clone()));

    if let [ProofTactic::SimpUsing(simp)] = tactics
        && let Some(proof) = root.try_restricted_simp_closure(&simp.premises)
    {
        return Ok(Some((proof.certificate(), proof.completed_proposition()?)));
    }

    if matches!(tactics, [ProofTactic::Simp])
        && let Some(proof) = root.try_simp_closure()?
    {
        return Ok(Some((proof.certificate(), proof.completed_proposition()?)));
    }

    // The checked Proof object currently owns the fixed-state and execution
    // instantiation paths, but pure theorem scripts still use the legacy
    // pure driver for this operation. Do not send an unsupported certificate
    // through the authoritative pure Proof path: that would turn a valid
    // script into a shape error before the pure driver can check it.
    if let Ok(certificate) = ProofCertificate::from_proof_tactics(tactics)
        && !proof_supports_pure_certificate(&certificate)
    {
        return Ok(None);
    }

    // Integer source binders must stay on the checked Proof path even when an
    // explicit step fails. The compatibility driver lowers raw source
    // variables as C expressions and can mask the real focused failure (for
    // example, an invalid `assumption` after a shadowing `intro`) with a
    // spurious zero-path lowering error.
    let has_integer_surface = surface_goal_contains_integer_quantifier(surface_goal);
    let checked = if has_integer_surface
        || tactics.iter().any(|tactic| {
            matches!(
                tactic,
                ProofTactic::ArithmeticUsing(_)
                    | ProofTactic::NormalizeUsing(_)
                    | ProofTactic::IntegerCertificate(_)
                    | ProofTactic::Witness(_)
                    | ProofTactic::Choose(_)
            )
        }) {
        root.try_authoritative_linear_script(tactics)?
    } else {
        root.try_linear_script(tactics)?
    };
    if let Some(proof) = checked {
        return Ok(Some((proof.certificate(), proof.completed_proposition()?)));
    }

    Ok(None)
}

fn surface_goal_contains_integer_quantifier(surface: &ClickProposition) -> bool {
    match surface {
        ClickProposition::ForAll {
            click_type, body, ..
        }
        | ClickProposition::Exists {
            click_type, body, ..
        } => *click_type == ClickType::Integer || surface_goal_contains_integer_quantifier(body),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            surface_goal_contains_integer_quantifier(left)
                || surface_goal_contains_integer_quantifier(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
        | ClickProposition::RangeAll { body, .. }
        | ClickProposition::RangeAny { body, .. } => surface_goal_contains_integer_quantifier(body),
        _ => false,
    }
}

fn pure_theorem_surface_certificate(
    theorem: &TheoremDefinition,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    surface_goal: &ClickProposition,
    source_tactics: Option<&[ProofTactic]>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<ProofCertificate, ClickError> {
    fn contains_restricted_simp(tactics: &[ProofTactic]) -> bool {
        tactics.iter().any(|tactic| match tactic {
            ProofTactic::Both(both) => {
                contains_restricted_simp(&both.left_tactics)
                    || contains_restricted_simp(&both.right_tactics)
            }
            ProofTactic::SimpUsing(_) => true,
            ProofTactic::If(proof_if) => {
                contains_restricted_simp(&proof_if.then_tactics)
                    || contains_restricted_simp(&proof_if.else_tactics)
            }
            ProofTactic::Cases(proof_cases) => {
                contains_restricted_simp(&proof_cases.left_tactics)
                    || contains_restricted_simp(&proof_cases.right_tactics)
            }
            ProofTactic::Have(have) => match &have.proof {
                SourceProof::Script(tactics) => contains_restricted_simp(tactics),
                _ => false,
            },
            _ => false,
        })
    }

    if let (Some(tactics), Some(setup)) = (source_tactics, induction_setup) {
        let lowered = lower_pure_induction_tactics(
            claim_label,
            context,
            predicate_environment,
            click_function_environment,
            &setup.surface_requires,
            &[],
            tactics,
            setup,
        )?;
        return ProofCertificate::from_proof_tactics(&lowered).map_err(|error| {
            ClickError::new(format!(
                "induction proof for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    if let Some(tactics) = source_tactics
        && let Ok(certificate) = ProofCertificate::from_proof_tactics(tactics)
    {
        return Ok(certificate);
    }

    if context.requires.contains(goal)
        || exactly_available_fact(goal, &context.requires).is_some()
        || quantified_equivalent_available_fact(goal, &context.requires).is_some()
    {
        return ProofCertificate::from_proof_tactics(&[ProofTactic::Assumption]).map_err(
            |error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid assumption certificate: {error:?}"
                ))
            },
        );
    }
    if matches!(normalize_proposition(goal), SimpProposition::True) {
        let tactics = plan_context_free_normalization(goal, surface_goal).ok_or_else(|| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` could not transcribe normalization as explicit structure"
            ))
        })?;
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid normalization certificate: {error:?}"
                ))
            });
    }
    let restricted_simp = source_tactics.and_then(|tactics| {
        let (last, prefix) = tactics.split_last()?;
        let ProofTactic::SimpUsing(simp) = last else {
            return None;
        };
        let unfolded_predicates = prefix
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some((unfolded_predicates, simp))
    });
    if let Some((unfolded_predicates, simp)) = restricted_simp {
        let available = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            &context.requires,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let explicit_goal = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            goal,
            &assumptions_from_propositions(&available),
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let premise_entries = simp
            .premises
            .iter()
            .map(|surface| {
                let kernel = lower_pure_theorem_proposition(
                    claim_label,
                    surface,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "smart `simp() using` for `{claim_label}` could not lower listed premise `{}`: {message}",
                        describe_click_proposition(surface)
                    ))
                })?;
                if available.iter().any(|fact| {
                    fact == &kernel || condition_polarity_equivalent(fact, &kernel)
                }) {
                    return Ok((kernel, surface.clone(), false));
                }
                if exact_fact_is_available(&kernel, &available) {
                    return Ok((kernel, surface.clone(), true));
                }
                Err(ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` lost exact listed premise `{}` during certificate generation",
                    describe_click_proposition(surface)
                )))
            })
            .collect::<Result<Vec<_>, ClickError>>()?;
        let premise_pairs = premise_entries
            .iter()
            .map(|(kernel, surface, _)| (kernel.clone(), surface.clone()))
            .collect::<Vec<_>>();
        let mut explicit =
            plan_restricted_simp_expansion(&explicit_goal, None, &premise_pairs).map_err(
                |error| {
                ClickError::new(format!(
                    "smart `simp() using` for `{claim_label}` has no explicit simple certificate: {}",
                    error.message()
                ))
            })?;
        let _ = remove_trailing_theorem_assumption(&mut explicit);
        let mut tactics = unfolded_predicates
            .into_iter()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(
            premise_entries
                .into_iter()
                .filter_map(|(_, surface, extract)| {
                    extract.then_some(ProofTactic::Extract(surface))
                }),
        );
        tactics.extend(explicit);
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart `simp() using` for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    let assumptions = assumptions_from_propositions(&context.requires);
    if let Some(plan) = plan_simp_certificate(goal, &assumptions)
        && let Some(tactics) =
            lower_pure_simp_certificate(theorem, context, goal, surface_goal, &plan)
    {
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid surface certificate: {error:?}"
            ))
        });
    }
    // Some bounded arithmetic facts are certified by a named kernel theorem
    // even when the general proposition-derivation API does not retain a
    // derivation tree. The simple surface certificate can still be selected
    // directly from the theorem's exact requirements.
    let premise_pairs = context
        .requires
        .iter()
        .enumerate()
        .filter_map(|(index, kernel)| {
            theorem
                .requires()
                .get(index)
                .and_then(Requirement::proposition)
                .cloned()
                .map(|surface| (kernel.clone(), surface))
        })
        .collect::<Vec<_>>();
    if premise_pairs.len() == context.requires.len()
        && let Some(mut tactics) = plan_explicit_named_signed_rule(goal, &premise_pairs)
    {
        let _ = remove_trailing_theorem_assumption(&mut tactics);
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid named-rule certificate: {error:?}"
            ))
        });
    }

    if let Some(tactics) = source_tactics
        && tactics.iter().any(|tactic| {
            matches!(
                tactic,
                ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. }
            )
        })
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_))
                || matches!(tactic, ProofTactic::Simp | ProofTactic::ApplyTheorem(_))
        })
    {
        // An applied theorem's conclusion is an available fact, so a
        // trailing smart `simp` lowers to the deterministic `assumption`,
        // and a bare `apply` lowers to `apply using` with the proved
        // theorem's own requires as the explicit premise pool.
        let requirement_premises = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .cloned()
            .collect::<Vec<_>>();
        let tactics = tactics
            .iter()
            .map(|tactic| match tactic {
                ProofTactic::Simp => ProofTactic::Assumption,
                ProofTactic::ApplyTheorem(application) => ProofTactic::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: requirement_premises.clone(),
                },
                other => other.clone(),
            })
            .collect::<Vec<_>>();
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid application certificate: {error:?}"
            ))
        });
    }

    if let Some(tactics) = source_tactics
        && tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Rewrite(_)))
        && tactics.iter().all(|tactic| {
            matches!(tactic.class(), TacticClass::Simple(_)) || matches!(tactic, ProofTactic::Simp)
        })
    {
        let tactics = tactics
            .iter()
            .map(|tactic| {
                if matches!(tactic, ProofTactic::Simp) {
                    ProofTactic::Normalize
                } else {
                    tactic.clone()
                }
            })
            .collect::<Vec<_>>();
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid rewrite certificate: {error:?}"
            ))
        });
    }

    if source_tactics.is_some_and(contains_restricted_simp) {
        return Err(ClickError::new(format!(
            "smart `simp() using` for `{claim_label}` is not yet lowerable with the surrounding proof structure; keep it as a standalone proof until Click has an explicit simple certificate for that structure"
        )));
    }

    let unfolded_predicates = source_tactics
        .unwrap_or_default()
        .iter()
        .filter_map(|tactic| match tactic {
            ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !unfolded_predicates.is_empty() {
        fn flatten_surface_conjunction(
            proposition: ClickProposition,
            flattened: &mut Vec<ClickProposition>,
        ) {
            match proposition {
                ClickProposition::And(left, right) => {
                    flatten_surface_conjunction(*left, flattened);
                    flatten_surface_conjunction(*right, flattened);
                }
                proposition => flattened.push(proposition),
            }
        }

        let unfolded = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .map(|premise| {
                unfold_structural_invariant_proposition(
                    predicate_environment,
                    premise,
                    &unfolded_predicates,
                )
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let mut premises = Vec::new();
        for proposition in unfolded {
            flatten_surface_conjunction(proposition, &mut premises);
        }
        let premise_pairs = premises
            .into_iter()
            .map(|surface| {
                let kernel = lower_pure_theorem_proposition(
                    claim_label,
                    &surface,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
                Ok((kernel, surface))
            })
            .collect::<Result<Vec<_>, ClickError>>()?;
        let available = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let explicit_goal = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
            goal,
            &assumptions_from_propositions(&available),
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let plan =
            plan_simp_certificate(&explicit_goal, &assumptions_from_propositions(&available))
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "smart proof for `{claim_label}` has no explicit proof after unfolding"
                    ))
                })?;
        let mut tactics = unfolded_predicates
            .into_iter()
            .map(ProofTactic::UnfoldPredicate)
            .collect::<Vec<_>>();
        tactics.extend(
            lower_restricted_simp_plan(&explicit_goal, None, &plan, &premise_pairs).map_err(
                |error| {
                    ClickError::new(format!(
                        "smart proof for `{claim_label}` has no explicit unfolded certificate: {}",
                        error.message()
                    ))
                },
            )?,
        );
        return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
            ClickError::new(format!(
                "smart proof for `{claim_label}` produced an invalid unfolded certificate: {error:?}"
            ))
        });
    }

    if matches!(source_tactics, Some([ProofTactic::Simp])) {
        let premise_pool = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .cloned()
            .collect::<Vec<_>>();
        if let Ok(tactics) = lower_pure_simp_after_function_unfold(
            claim_label,
            context,
            surface_goal,
            predicate_environment,
            click_function_environment,
            &premise_pool,
            &[],
        ) {
            return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid function-unfold certificate: {error:?}"
                ))
            });
        }
    }

    if let Some(tactics) = source_tactics
        && tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::If(_)))
    {
        let premise_pool = theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
            .cloned()
            .collect::<Vec<_>>();
        if let Some(tactics) = lower_pure_branching_tactics(
            claim_label,
            context,
            goal,
            predicate_environment,
            click_function_environment,
            &premise_pool,
            tactics,
        ) {
            return ProofCertificate::from_proof_tactics(&tactics).map_err(|error| {
                ClickError::new(format!(
                    "smart proof for `{claim_label}` produced an invalid branching certificate: {error:?}"
                ))
            });
        }
    }

    Err(ClickError::new(format!(
        "smart proof for `{claim_label}` succeeded but did not produce a pure surface certificate"
    )))
}

/// Lowers a branching pure proof script to deterministic tactics: each `if`
/// keeps its shape while contributing its (negated) condition to the branch's
/// premise pool, and each closing `simp` becomes an explicit proof of the goal
/// from exactly that pool.
fn lower_pure_branching_tactics(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
    tactics: &[ProofTactic],
) -> Option<Vec<ProofTactic>> {
    let mut lowered = Vec::new();
    for tactic in tactics {
        match tactic {
            ProofTactic::If(proof_if) => {
                let mut then_pool = premise_pool.to_vec();
                then_pool.push(proof_if.condition.clone());
                let mut else_pool = premise_pool.to_vec();
                else_pool.push(ClickProposition::Not(Box::new(proof_if.condition.clone())));
                lowered.push(ProofTactic::If(ProofIf {
                    condition: proof_if.condition.clone(),
                    then_tactics: lower_pure_branching_tactics(
                        claim_label,
                        context,
                        goal,
                        predicate_environment,
                        click_function_environment,
                        &then_pool,
                        &proof_if.then_tactics,
                    )?,
                    else_tactics: lower_pure_branching_tactics(
                        claim_label,
                        context,
                        goal,
                        predicate_environment,
                        click_function_environment,
                        &else_pool,
                        &proof_if.else_tactics,
                    )?,
                }));
            }
            ProofTactic::Simp => {
                lowered.extend(
                    lower_pure_simp_from_premise_pool(
                        claim_label,
                        context,
                        goal,
                        predicate_environment,
                        click_function_environment,
                        premise_pool,
                    )
                    .ok()?,
                );
            }
            tactic if matches!(tactic.class(), TacticClass::Simple(_)) => {
                lowered.push(tactic.clone());
            }
            _ => return None,
        }
    }
    Some(lowered)
}

fn lower_pure_simp_from_premise_pool(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
) -> Result<Vec<ProofTactic>, ClickError> {
    lower_pure_simp_from_mixed_premise_pool(
        claim_label,
        context,
        goal,
        predicate_environment,
        click_function_environment,
        premise_pool,
        &[],
    )
}

#[allow(clippy::too_many_arguments)]
fn lower_pure_arithmetic_from_premise_pool(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
) -> Result<Vec<ProofTactic>, ClickError> {
    if crate::kernel::proof::fact_reasoning::check_signed_affine_arithmetic(goal, &[]).is_ok() {
        return Ok(vec![ProofTactic::ArithmeticUsing(Vec::new())]);
    }
    for surface in premise_pool {
        let kernel = lower_pure_theorem_proposition(
            claim_label,
            surface,
            &context.values,
            &context.array_refs,
            &context.memory,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        if crate::kernel::proof::fact_reasoning::check_signed_affine_arithmetic(
            goal,
            std::slice::from_ref(&kernel),
        )
        .is_ok()
        {
            return Ok(vec![ProofTactic::ArithmeticUsing(vec![surface.clone()])]);
        }
    }
    Err(ClickError::new(
        "no single available arithmetic premise proves the goal",
    ))
}

#[allow(clippy::too_many_arguments)]
fn lower_pure_simp_from_mixed_premise_pool(
    claim_label: &str,
    context: &PureTheoremContext,
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
    opaque_premise_pool: &[ClickProposition],
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut premise_pairs = premise_pool
        .iter()
        .map(|surface| {
            let lower = if opaque_premise_pool.contains(surface) {
                lower_pure_theorem_proposition_opaque
            } else {
                lower_pure_theorem_proposition
            };
            let kernel = lower(
                claim_label,
                surface,
                &context.values,
                &context.array_refs,
                &context.memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
            Ok((kernel, surface.clone()))
        })
        .collect::<Result<Vec<_>, ClickError>>()?;
    add_canonical_order_premise_pairs(
        claim_label,
        context,
        predicate_environment,
        click_function_environment,
        &mut premise_pairs,
    )?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    if let Some(tactics) = plan_explicit_named_signed_rule(goal, &premise_pairs) {
        return Ok(tactics);
    }
    let certificate = plan_simp_certificate(goal, &assumptions_from_propositions(&available))
        .ok_or_else(|| {
            ClickError::new("smart simplification produced no proposition derivation")
        })?;
    lower_restricted_simp_plan(goal, None, &certificate, &premise_pairs)
}

#[allow(clippy::too_many_arguments)]
fn lower_pure_simp_after_function_unfold(
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
    opaque_premise_pool: &[ClickProposition],
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut premise_pairs = premise_pool
        .iter()
        .map(|surface| {
            let lower = if opaque_premise_pool.contains(surface) {
                lower_pure_theorem_proposition_opaque
            } else {
                lower_pure_theorem_proposition
            };
            let kernel = lower(
                claim_label,
                surface,
                &context.values,
                &context.array_refs,
                &context.memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
            Ok((kernel, surface.clone()))
        })
        .collect::<Result<Vec<_>, ClickError>>()?;
    add_canonical_order_premise_pairs(
        claim_label,
        context,
        predicate_environment,
        click_function_environment,
        &mut premise_pairs,
    )?;
    let available = premise_pairs
        .iter()
        .map(|(kernel, _)| kernel.clone())
        .collect::<Vec<_>>();
    let assumptions = assumptions_from_propositions(&available);
    let state = CState::new().with_memory(context.memory.clone());
    let mut unfolded_surface_goal = surface_goal.clone();
    let mut tactics = Vec::new();
    let surface_facts = premise_pairs
        .iter()
        .map(|(_, surface)| surface.clone())
        .collect::<Vec<_>>();
    let mut unfolded_applications = Vec::new();
    // Expand one breadth-first layer beyond the calls present in the goal. This
    // lets sibling calls expose mutually recursive IH instances before either
    // sibling is expanded recursively again, while keeping the smart tactic's
    // search finite and proportional to the goal's explicit call frontier.
    let mut pending_applications =
        click_function_applications(&unfolded_surface_goal, &surface_facts)
            .into_iter()
            .map(|application| (application, true))
            .collect::<Vec<_>>();
    let mut pending_index = 0;
    while let Some((application, expose_children)) =
        pending_applications.get(pending_index).cloned()
    {
        pending_index += 1;
        if unfolded_applications.contains(&application) {
            continue;
        }
        let definition = click_function_environment
            .get(&application.name)
            .ok_or_else(|| {
                ClickError::new(format!("unknown pure function `{}`", application.name))
            })?;
        let variable_types = generics::concrete_variable_types(&context.values, &BTreeMap::new());
        let definition = generics::instantiate_function_for_surface_call_with_variables(
            definition,
            &application.arguments,
            &variable_types,
        )
        .map_err(ClickError::new)?;
        let substitutions = definition
            .parameters()
            .iter()
            .zip(&application.arguments)
            .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
            .collect::<BTreeMap<_, _>>();
        let surface_body = substitute_contract_expression(definition.body(), &substitutions)
            .map_err(ClickError::new)?;
        if expose_children {
            for exposed in click_function_applications_in_expression(&surface_body, &surface_facts)
            {
                if !pending_applications
                    .iter()
                    .any(|(queued, _)| queued == &exposed)
                {
                    pending_applications.push((exposed, false));
                }
            }
        }
        let surface_equality = ClickProposition::Comparison {
            left: ContractExpression::Call {
                name: application.name.clone(),
                arguments: application.arguments.clone(),
            },
            operator: ComparisonOperator::Equal,
            right: surface_body,
        };
        let Some(next_surface_goal) = rewrite_click_proposition_by_surface_equality(
            &unfolded_surface_goal,
            &surface_equality,
        ) else {
            continue;
        };
        unfolded_surface_goal = next_surface_goal;
        unfolded_applications.push(application.clone());
        tactics.push(ProofTactic::UnfoldFunction(application));

        let mut opaque_calls = BTreeSet::new();
        crate::surface::validation::collect_click_function_calls_in_proposition(
            &unfolded_surface_goal,
            &mut opaque_calls,
        );
        let refreshed_goal =
            lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_integer_values(
                &unfolded_surface_goal,
                &assumptions,
                &context.values,
                &context.array_refs,
                &context.integer_values,
                &state,
                &state,
                None,
                &RecordedSnapshots::new(),
                predicate_environment,
                click_function_environment,
                &opaque_calls,
            )
            .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        let Some(plan) = plan_simp_certificate(&refreshed_goal, &assumptions) else {
            continue;
        };
        tactics.extend(lower_restricted_simp_plan(
            &refreshed_goal,
            None,
            &plan,
            &premise_pairs,
        )?);
        return Ok(tactics);
    }
    Err(ClickError::new(format!(
        "smart simplification still has no derivation after unfolding {} outer pure function call{}",
        tactics.len(),
        if tactics.len() == 1 { "" } else { "s" },
    )))
}

fn click_function_applications_in_expression(
    expression: &ContractExpression,
    known_facts: &[ClickProposition],
) -> Vec<ClickFunctionApplication> {
    click_function_applications(
        &ClickProposition::Comparison {
            left: expression.clone(),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        },
        known_facts,
    )
}

fn add_canonical_order_premise_pairs(
    claim_label: &str,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pairs: &mut Vec<(Proposition, ClickProposition)>,
) -> Result<(), ClickError> {
    let originals = premise_pairs.clone();
    for (available, surface) in originals {
        let ClickProposition::Not(body) = surface else {
            continue;
        };
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = *body
        else {
            continue;
        };
        let canonical = match operator {
            ComparisonOperator::LessEqual => ClickProposition::Comparison {
                left: right,
                operator: ComparisonOperator::LessThan,
                right: left,
            },
            ComparisonOperator::LessThan => ClickProposition::Comparison {
                left: right,
                operator: ComparisonOperator::LessEqual,
                right: left,
            },
            ComparisonOperator::GreaterEqual => ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::LessThan,
                right,
            },
            ComparisonOperator::GreaterThan => ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::LessEqual,
                right,
            },
            ComparisonOperator::Equal | ComparisonOperator::NotEqual | ComparisonOperator::In => {
                continue;
            }
        };
        let kernel = lower_pure_theorem_proposition(
            claim_label,
            &canonical,
            &context.values,
            &context.array_refs,
            &context.memory,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        if condition_polarity_equivalent(&available, &kernel)
            && !premise_pairs.iter().any(|(_, form)| form == &canonical)
        {
            premise_pairs.push((kernel, canonical));
        }
    }
    Ok(())
}

pub(super) fn click_function_applications(
    proposition: &ClickProposition,
    known_facts: &[ClickProposition],
) -> Vec<ClickFunctionApplication> {
    fn fact_polarity(
        proposition: &ClickProposition,
        known_facts: &[ClickProposition],
    ) -> Option<bool> {
        if known_facts.contains(proposition) {
            return Some(true);
        }
        let negated = ClickProposition::Not(Box::new(proposition.clone()));
        known_facts.contains(&negated).then_some(false)
    }

    fn expression(
        term: &ContractExpression,
        known_facts: &[ClickProposition],
        applications: &mut Vec<ClickFunctionApplication>,
    ) {
        match term {
            ContractExpression::IntegerLiteral(_) => {}
            ContractExpression::Negate(inner) => expression(inner, known_facts, applications),
            ContractExpression::ResourceField(_)
            | ContractExpression::AlgebraicVariable { .. }
            | ContractExpression::Binding(_) => {}
            ContractExpression::AlgebraicConstructor { arguments, .. } => {
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                expression(scrutinee, known_facts, applications);
                for arm in arms {
                    expression(&arm.body, known_facts, applications);
                }
            }
            ContractExpression::SequenceLiteral(elements) => {
                for element in elements {
                    expression(element, known_facts, applications);
                }
            }
            ContractExpression::SequenceConcat(left, right) => {
                expression(left, known_facts, applications);
                expression(right, known_facts, applications);
            }
            ContractExpression::Call { name, arguments } => {
                let application = ClickFunctionApplication {
                    name: name.clone(),
                    arguments: arguments.clone(),
                };
                if !applications.contains(&application) {
                    applications.push(application);
                }
            }
            ContractExpression::Field { base, .. }
            | ContractExpression::Old(base)
            | ContractExpression::At {
                expression: base, ..
            }
            | ContractExpression::BitwiseNot(base) => expression(base, known_facts, applications),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right)
            | ContractExpression::Divide(left, right)
            | ContractExpression::Remainder(left, right)
            | ContractExpression::ShiftLeft(left, right)
            | ContractExpression::ShiftRight(left, right)
            | ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right)
            | ContractExpression::Index(left, right) => {
                expression(left, known_facts, applications);
                expression(right, known_facts, applications);
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                proposition_inner(condition, known_facts, applications);
                match fact_polarity(condition, known_facts) {
                    Some(true) => expression(then_branch, known_facts, applications),
                    Some(false) => expression(else_branch, known_facts, applications),
                    None => {}
                }
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                expression(start, known_facts, applications);
                expression(end, known_facts, applications);
                expression(initial, known_facts, applications);
                expression(body, known_facts, applications);
            }
            ContractExpression::Let { value, body, .. } => {
                expression(value, known_facts, applications);
                expression(body, known_facts, applications);
            }
            ContractExpression::ResourceCount(resource) => {
                if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                    for argument in arguments {
                        expression(argument, known_facts, applications);
                    }
                }
            }
            ContractExpression::QualifiedC { .. }
            | ContractExpression::CFragment(_)
            | ContractExpression::CBinding(_)
            | ContractExpression::ResourceWildcard => {}
        }
    }

    fn proposition_inner(
        proposition: &ClickProposition,
        known_facts: &[ClickProposition],
        applications: &mut Vec<ClickFunctionApplication>,
    ) {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                expression(left, known_facts, applications);
                expression(right, known_facts, applications);
            }
            ClickProposition::FloatClassification {
                expression: value, ..
            } => {
                expression(value, known_facts, applications);
            }
            ClickProposition::Defined { expression: value } => {
                expression(value, known_facts, applications)
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                proposition_inner(left, known_facts, applications);
                proposition_inner(right, known_facts, applications);
            }
            ClickProposition::Not(body)
            | ClickProposition::At {
                proposition: body, ..
            }
            | ClickProposition::ForAll { body, .. }
            | ClickProposition::Exists { body, .. } => {
                proposition_inner(body, known_facts, applications)
            }
            ClickProposition::RangeAll {
                start, end, body, ..
            }
            | ClickProposition::RangeAny {
                start, end, body, ..
            } => {
                expression(start, known_facts, applications);
                expression(end, known_facts, applications);
                proposition_inner(body, known_facts, applications);
            }
            ClickProposition::PredicateCall { arguments, .. } => {
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
            }
            ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => {}
        }
    }

    let mut applications = Vec::new();
    proposition_inner(proposition, known_facts, &mut applications);
    applications
}

fn induction_application_surface_premises(
    setup: &PureInductionSetup,
    argument: &ContractExpression,
) -> Result<Vec<ClickProposition>, ClickError> {
    let zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
    let current = ContractExpression::CFragment(CExpression::Variable(setup.parameter.clone()));
    let mut premises = vec![
        ClickProposition::Comparison {
            left: zero,
            operator: ComparisonOperator::LessEqual,
            right: argument.clone(),
        },
        ClickProposition::Comparison {
            left: argument.clone(),
            operator: ComparisonOperator::LessThan,
            right: current,
        },
    ];
    for requirement in &setup.surface_requires {
        let substituted = substitute_click_proposition(
            requirement,
            &BTreeMap::from([(setup.parameter.clone(), argument.clone())]),
        )
        .map_err(ClickError::new)?;
        if !premises.contains(&substituted) {
            premises.push(substituted);
        }
    }
    Ok(premises)
}

fn lower_pure_induction_tactics(
    claim_label: &str,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    premise_pool: &[ClickProposition],
    opaque_premise_pool: &[ClickProposition],
    tactics: &[ProofTactic],
    setup: &PureInductionSetup,
) -> Result<Vec<ProofTactic>, ClickError> {
    let mut lowered = Vec::new();
    let mut current_pool = premise_pool.to_vec();
    let mut current_opaque_pool = opaque_premise_pool.to_vec();
    for tactic in tactics {
        match tactic {
            ProofTactic::If(proof_if) => {
                let mut then_pool = current_pool.clone();
                then_pool.push(proof_if.condition.clone());
                let mut else_pool = current_pool.clone();
                else_pool.push(ClickProposition::Not(Box::new(proof_if.condition.clone())));
                let then_opaque_pool = current_opaque_pool.clone();
                let else_opaque_pool = current_opaque_pool.clone();
                lowered.push(ProofTactic::If(ProofIf {
                    condition: proof_if.condition.clone(),
                    then_tactics: lower_pure_induction_tactics(
                        claim_label,
                        context,
                        predicate_environment,
                        click_function_environment,
                        &then_pool,
                        &then_opaque_pool,
                        &proof_if.then_tactics,
                        setup,
                    )?,
                    else_tactics: lower_pure_induction_tactics(
                        claim_label,
                        context,
                        predicate_environment,
                        click_function_environment,
                        &else_pool,
                        &else_opaque_pool,
                        &proof_if.else_tactics,
                        setup,
                    )?,
                }));
            }
            ProofTactic::ApplyInduction {
                hypothesis,
                argument,
            } => {
                let application_premises = induction_application_surface_premises(setup, argument)?;
                for premise in &application_premises {
                    if current_pool.contains(premise) {
                        continue;
                    }
                    let lowered_goal = lower_pure_theorem_proposition(
                        claim_label,
                        premise,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
                    let current_kernels = current_pool
                        .iter()
                        .map(|surface| {
                            lower_pure_theorem_proposition(
                                claim_label,
                                surface,
                                &context.values,
                                &context.array_refs,
                                &context.memory,
                                predicate_environment,
                                click_function_environment,
                            )
                            .map_err(|message| {
                                ClickError::new(format!("`{claim_label}`: {message}"))
                            })
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if exact_fact_is_available(&lowered_goal, &current_kernels) {
                        continue;
                    }
                    let proof = lower_pure_simp_from_premise_pool(
                        claim_label,
                        context,
                        &lowered_goal,
                        predicate_environment,
                        click_function_environment,
                        &current_pool,
                    )
                    .or_else(|simp_error| {
                        lower_pure_arithmetic_from_premise_pool(
                            claim_label,
                            context,
                            &lowered_goal,
                            predicate_environment,
                            click_function_environment,
                            &current_pool,
                        )
                        .map_err(|arithmetic_error| {
                            ClickError::new(format!(
                                "{}; arithmetic fallback: {}",
                                simp_error.message(),
                                arithmetic_error.message(),
                            ))
                        })
                    })
                    .map_err(|error| {
                        ClickError::new(format!(
                            "induction hypothesis application in `{claim_label}` could not produce an explicit proof of `{}`: {}",
                            describe_click_proposition(premise),
                            error.message()
                        ))
                    })?;
                    lowered.push(ProofTactic::Have(ProofHave {
                        proposition: premise.clone(),
                        proof: SourceProof::Script(proof),
                    }));
                    current_pool.push(premise.clone());
                }
                let substituted = substitute_click_proposition(
                    &setup.surface_goal,
                    &BTreeMap::from([(setup.parameter.clone(), argument.clone())]),
                )
                .map_err(ClickError::new)?;
                lowered.push(ProofTactic::ApplyInductionUsing {
                    hypothesis: hypothesis.clone(),
                    argument: argument.clone(),
                    premises: application_premises,
                });
                if !current_pool.contains(&substituted) {
                    current_pool.push(substituted.clone());
                }
                if !current_opaque_pool.contains(&substituted) {
                    current_opaque_pool.push(substituted);
                }
            }
            ProofTactic::ApplyInductionUsing {
                hypothesis,
                argument,
                premises,
            } => {
                let substituted = substitute_click_proposition(
                    &setup.surface_goal,
                    &BTreeMap::from([(setup.parameter.clone(), argument.clone())]),
                )
                .map_err(ClickError::new)?;
                lowered.push(ProofTactic::ApplyInductionUsing {
                    hypothesis: hypothesis.clone(),
                    argument: argument.clone(),
                    premises: premises.clone(),
                });
                if !current_pool.contains(&substituted) {
                    current_pool.push(substituted.clone());
                }
                if !current_opaque_pool.contains(&substituted) {
                    current_opaque_pool.push(substituted);
                }
            }
            ProofTactic::Have(have) => {
                lowered.push(ProofTactic::Have(have.clone()));
                if !current_pool.contains(&have.proposition) {
                    current_pool.push(have.proposition.clone());
                }
            }
            ProofTactic::Simp => {
                let explicit_goal = lower_pure_theorem_proposition(
                    claim_label,
                    &setup.surface_goal,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
                let direct = lower_pure_simp_from_mixed_premise_pool(
                    claim_label,
                    context,
                    &explicit_goal,
                    predicate_environment,
                    click_function_environment,
                    &current_pool,
                    &current_opaque_pool,
                );
                let explicit = match direct {
                    Ok(explicit) => explicit,
                    Err(direct_error) => lower_pure_simp_after_function_unfold(
                        claim_label,
                        context,
                        &setup.surface_goal,
                        predicate_environment,
                        click_function_environment,
                        &current_pool,
                        &current_opaque_pool,
                    )
                    .map_err(|error| {
                        ClickError::new(format!(
                            "induction `simp` in `{claim_label}` could not produce an explicit simple proof: {}\n  direct simplification: {}",
                            error.message(),
                            direct_error.message()
                        ))
                    })?,
                };
                lowered.extend(explicit);
            }
            tactic if matches!(tactic.class(), TacticClass::Simple(_)) => {
                lowered.push(tactic.clone());
            }
            _ => {
                return Err(ClickError::new(format!(
                    "pure induction currently cannot lower smart tactic `{}`; keep the step proof explicit",
                    tactic_name(tactic)
                )));
            }
        }
    }
    Ok(lowered)
}

/// Applies a validated surface proof through the checked pure-tactic driver.
///
/// The certificate is serialization input only. Its tactics advance the same
/// persistent `Proof` operations used by ordinary source scripts; no parallel
/// certificate interpreter participates in acceptance.
#[allow(clippy::too_many_arguments)]
pub(super) fn validate_pure_theorem_certificate(
    claim_label: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    certificate: &ProofCertificate,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<Option<crate::kernel::proof::CheckedProposition>, ClickError> {
    if proof_supports_pure_certificate(certificate) {
        let root = match induction_setup {
            Some(setup) => Proof::for_pure_surface_goal_with_induction(
                claim_label,
                requires,
                goal.clone(),
                setup.surface_goal.clone(),
                context,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                setup.clone(),
            ),
            None => Proof::for_pure_goal(
                claim_label,
                requires,
                goal.clone(),
                context,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            ),
        };
        let tactics = certificate.to_proof_tactics();
        let Some(proof) = root.try_authoritative_linear_script(&tactics)? else {
            return Err(ClickError::new(format!(
                "pure goal `{claim_label}` certificate ended before closing its goal"
            )));
        };
        debug_assert!(proof.is_complete());
        return Ok(Some(proof.completed_proposition()?));
    }
    if induction_setup.is_some() {
        return Err(ClickError::new(format!(
            "pure induction certificate for `{claim_label}` contains a step not supported by the checked Proof object"
        )));
    }
    // The legacy pure driver checks the script without building a kernel
    // proof object, so it issues no completion and the theorem contributes no
    // whole-contract authority.
    prove_pure_theorem_script(
        claim_label,
        requires,
        goal,
        None,
        predicate_environment,
        click_function_environment,
        theorem_environment,
        context,
        &certificate.to_proof_tactics(),
        induction_setup,
    )?;
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_theorem_script(
    claim_label: &str,
    requires: &[Proposition],
    goal: &Proposition,
    surface_goal: Option<&ClickProposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    tactics: &[ProofTactic],
    induction_setup: Option<&PureInductionSetup>,
) -> Result<(), ClickError> {
    for proof_case in expand_proof_if_cases(tactics)? {
        prove_pure_theorem_tactics(
            claim_label,
            requires,
            goal,
            surface_goal,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            context,
            &proof_case,
            induction_setup,
        )?;
    }
    Ok(())
}

pub(super) fn lower_pure_theorem_proposition(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_opaque_calls(
        theorem_name,
        proposition,
        values,
        array_refs,
        memory,
        predicate_environment,
        click_function_environment,
        &BTreeSet::new(),
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_with_integer_values(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_algebraic_and_integer_values(
        theorem_name,
        proposition,
        values,
        array_refs,
        &BTreeMap::new(),
        integer_values,
        memory,
        predicate_environment,
        click_function_environment,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_with_algebraic_and_integer_values(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_recording_introductions(
        theorem_name,
        proposition,
        &PureFactContext::new(),
        values,
        array_refs,
        algebraic_values,
        integer_values,
        memory,
        predicate_environment,
        click_function_environment,
    )
    .map(|(proposition, _)| proposition)
}

/// The pure-theorem lowering, also returning the head chain the kernel
/// recorded. A pure goal keeps that record so its introductions read the
/// exact binder the lowering chose rather than reconstructing one.
#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_recording_introductions(
    theorem_name: &str,
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(Proposition, crate::kernel::LoweringIntroductions), String> {
    let state = CState::new().with_memory(memory.clone());
    lower_fixed_state_proposition_through_kernel_recording_introductions(
        proposition,
        &PureFactContext::new(),
        assumptions,
        values,
        array_refs,
        algebraic_values,
        integer_values,
        &state,
        &state,
        None,
        &RecordedSnapshots::new(),
        predicate_environment,
        click_function_environment,
        &BTreeSet::new(),
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_with_algebraic_values(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_algebraic_and_integer_values(
        theorem_name,
        proposition,
        values,
        array_refs,
        algebraic_values,
        &crate::persistent::PersistentMap::default(),
        memory,
        predicate_environment,
        click_function_environment,
    )
}

/// A pure theorem's proposition lowered at its parameter state by the
/// kernel, with the calls named in `opaque_click_functions` kept as
/// applications.
#[allow(clippy::too_many_arguments)]
fn lower_pure_theorem_proposition_with_opaque_calls(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    opaque_click_functions: &BTreeSet<String>,
) -> Result<Proposition, String> {
    let state = CState::new().with_memory(memory.clone());
    lower_fixed_state_proposition_through_kernel_with_opaque_calls(
        proposition,
        &PureFactContext::new(),
        values,
        array_refs,
        &state,
        &state,
        None,
        &RecordedSnapshots::new(),
        predicate_environment,
        click_function_environment,
        opaque_click_functions,
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

fn lower_pure_theorem_proposition_opaque(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let opaque = click_function_environment
        .definitions
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    lower_pure_theorem_proposition_with_opaque_calls(
        theorem_name,
        proposition,
        values,
        array_refs,
        memory,
        predicate_environment,
        click_function_environment,
        &opaque,
    )
}

#[allow(clippy::too_many_arguments)]
fn apply_pure_induction_hypothesis(
    setup: &PureInductionSetup,
    hypothesis: &str,
    argument: &ContractExpression,
    explicit_surface_premises: Option<&[ClickProposition]>,
    claim_label: &str,
    tactic_index: usize,
    available: &mut Vec<Proposition>,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    if hypothesis != setup.hypothesis {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown induction hypothesis `{hypothesis}`"
        )));
    }
    let state = CState::new().with_memory(context.memory.clone());
    let explicit_premises = explicit_surface_premises
        .map(|premises| {
            premises
                .iter()
                .map(|premise| {
                    lower_pure_theorem_proposition(
                        claim_label,
                        premise,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                        ))
                    })
                })
                .collect::<Result<Vec<_>, _>>()
        })
        .transpose()?;
    if let Some(premises) = &explicit_premises {
        for premise in premises {
            if !exact_fact_is_available(premise, available) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `apply using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }
    }
    let reasoning_facts = explicit_premises.as_deref().unwrap_or(available);
    let assumptions = assumptions_from_propositions(reasoning_facts);
    let mut active_functions = BTreeSet::new();
    let value = evaluate_contract_expression_with_environment(
        &context.values,
        &context.array_refs,
        &state,
        &state,
        None,
        &assumptions,
        argument,
        predicate_environment,
        click_function_environment,
        &RecordedSnapshots::new(),
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not evaluate induction argument: {message}"
        ))
    })?;
    let CValue::Int32(argument_term) = value else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction argument must have type int32"
        )));
    };
    let Some(CValue::Int32(current_term)) = context.values.get(&setup.parameter) else {
        return Err(ClickError::new("invalid induction parameter binding"));
    };
    let nonnegative = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(argument_term.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let smaller = Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(argument_term.clone()),
            Box::new(current_term.clone()),
        ),
        true,
    );
    let proves = |fact: &Proposition| {
        available.contains(fact)
            || assumptions.derive_proposition(fact).is_some()
            || matches!(
                fact,
                Proposition::ConditionIs(condition, value)
                    if assumptions.decide(condition) == Some(*value)
            )
            || matches!(simp_proposition(fact, &assumptions), SimpProposition::True)
    };
    fn positive_subtraction_step(term: &Bitvector32Term, current: &Bitvector32Term) -> Option<u32> {
        let Bitvector32Term::Subtract(left, right) = term else {
            return None;
        };
        let step = right.as_const()?;
        if step == 0 {
            return None;
        }
        let prior = if left.as_ref() == current {
            0
        } else {
            positive_subtraction_step(left, current)?
        };
        prior
            .checked_add(step)
            .filter(|total| *total <= i32::MAX as u32)
    }
    let positive_subtraction = match positive_subtraction_step(&argument_term, current_term) {
        Some(step) => {
            let enough = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(current_term.clone()),
                    Box::new(Bitvector32Term::Constant(step)),
                ),
                true,
            );
            explicit_premises.is_none()
                && (proves(&nonnegative)
                    || proves(&enough)
                    || assumptions.decide(&ConditionTerm::Bitvector32SignedLessEqual(
                        Box::new(current_term.clone()),
                        Box::new(Bitvector32Term::Constant(step - 1)),
                    )) == Some(false))
        }
        None => false,
    };
    if !proves(&smaller) && !positive_subtraction {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction hypothesis argument is not proved smaller than `{}`",
            setup.parameter
        )));
    }
    if !proves(&nonnegative) && !positive_subtraction {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction hypothesis argument is not proved nonnegative: {nonnegative:?}\n  available: {available:#?}"
        )));
    }
    if !available.contains(&nonnegative) {
        available.push(nonnegative.clone());
    }
    if !available.contains(&smaller) {
        available.push(smaller.clone());
    }
    let reasoning_facts = explicit_premises.as_deref().unwrap_or(available);
    let assumptions = assumptions_from_propositions(reasoning_facts);
    let proves = |fact: &Proposition| {
        available.contains(fact)
            || assumptions.derive_proposition(fact).is_some()
            || matches!(
                fact,
                Proposition::ConditionIs(condition, value)
                    if assumptions.decide(condition) == Some(*value)
            )
            || matches!(simp_proposition(fact, &assumptions), SimpProposition::True)
    };
    let mut values = context.values.clone();
    values.insert(
        setup.parameter.clone(),
        CValue::Int32(argument_term.clone()),
    );
    let mut application_premises = vec![nonnegative.clone(), smaller.clone()];
    for requirement in &setup.surface_requires {
        let requirement = lower_pure_theorem_proposition_opaque(
            claim_label,
            requirement,
            &values,
            &context.array_refs,
            &context.memory,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
        if requirement != nonnegative && !proves(&requirement) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: induction hypothesis requirement is unavailable: {requirement:?}"
            )));
        }
        application_premises.push(requirement);
    }
    let conclusion = lower_pure_theorem_proposition_opaque(
        claim_label,
        &setup.surface_goal,
        &values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}`: {message}")))?;
    let quantified = pure_induction_hypothesis(
        setup,
        context,
        predicate_environment,
        click_function_environment,
    )?;
    if !available.contains(&quantified) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: induction hypothesis is not active"
        )));
    }
    let theorem = prove_forall_int32_application(
        &quantified,
        argument_term,
        &application_premises,
    )
    .ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: kernel rejected induction hypothesis instantiation"
        ))
    })?;
    let Proposition::Implies(theorem_quantified, mut theorem_body) = theorem.proposition().clone()
    else {
        return Err(ClickError::new("invalid induction application theorem"));
    };
    if theorem_quantified.as_ref() != &quantified {
        return Err(ClickError::new(
            "induction theorem changed its quantified premise",
        ));
    }
    for premise in &application_premises {
        let Proposition::Implies(theorem_premise, body) = theorem_body.as_ref() else {
            return Err(ClickError::new(
                "induction theorem omitted an application premise",
            ));
        };
        if theorem_premise.as_ref() != premise {
            return Err(ClickError::new(
                "induction theorem changed an application premise",
            ));
        }
        theorem_body = body.clone();
    }
    if theorem_body.as_ref() != &conclusion {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: kernel induction conclusion does not match `{hypothesis}`"
        )));
    }
    if !available.contains(&conclusion) {
        available.push(conclusion);
    }
    Ok(())
}

fn prove_pure_theorem_goal(
    claim_label: &str,
    proof_name: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    theorem_applications: &[(usize, TheoremApplication)],
    unfolded_predicates: &[String],
    use_simp: bool,
) -> Result<(), ClickError> {
    let mut available = unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        requires,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` failed: {message}")))?;
    let state = CState::new().with_memory(context.memory.clone());
    let recorded_snapshots = RecordedSnapshots::new();
    let application_context = TheoremApplicationContext {
        values: &context.values,
        array_refs: &context.array_refs,
        pre_state: &state,
        post_state: &state,
        result: None,
        recorded_snapshots: &recorded_snapshots,
        integer_values: &context.integer_values,
    };
    available = apply_theorem_applications_to_available(
        theorem_environment,
        theorem_applications,
        claim_label,
        None,
        available,
        &application_context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        goal,
        &assumptions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` failed: {message}")))?;
    if available.contains(&goal) {
        return Ok(());
    }
    if use_simp {
        match simp_proposition(&goal, &assumptions) {
            SimpProposition::True => return Ok(()),
            _ => {
                return Err(ClickError::new(format!(
                    "`{proof_name}` failed for `{claim_label}`: simplified proposition was not true: {}\n  {}",
                    describe_pure_fact(&goal, &[], &[]),
                    describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                )));
            }
        }
    }

    Err(ClickError::new(format!(
        "`{proof_name}` failed for `{claim_label}`: {}",
        describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
    )))
}

#[allow(clippy::too_many_arguments)]
fn prove_pure_theorem_tactics(
    claim_label: &str,
    requires: &[Proposition],
    original_goal: &Proposition,
    original_surface_goal: Option<&ClickProposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    proof_case: &ExpandedProofCase,
    induction_setup: Option<&PureInductionSetup>,
) -> Result<(), ClickError> {
    let state = CState::new().with_memory(context.memory.clone());
    let recorded_snapshots = RecordedSnapshots::new();
    let application_context = TheoremApplicationContext {
        values: &context.values,
        array_refs: &context.array_refs,
        pre_state: &state,
        post_state: &state,
        result: None,
        recorded_snapshots: &recorded_snapshots,
        integer_values: &context.integer_values,
    };
    let mut available = requires.to_vec();
    let mut unfolded_predicates = Vec::new();
    let mut goal = original_goal.clone();
    let mut surface_goal = original_surface_goal
        .cloned()
        .or_else(|| induction_setup.map(|setup| setup.surface_goal.clone()));
    let mut closed = false;
    let mut induction_active = false;

    for (tactic_index, tactic) in proof_case.tactics.iter().enumerate() {
        for assumption in proof_case
            .assumptions
            .iter()
            .filter(|assumption| assumption.tactic_index == tactic_index)
        {
            match &assumption.kind {
                ProofCaseAssumptionKind::Condition { proposition, value } => {
                    let proposition = lower_pure_theorem_proposition(
                        claim_label,
                        proposition,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
                        ))
                    })?;
                    available.push(if *value {
                        proposition
                    } else {
                        Proposition::Not(Box::new(proposition))
                    });
                }
                ProofCaseAssumptionKind::Disjunct { disjunction, left } => {
                    let lowered = lower_pure_theorem_proposition(
                        claim_label,
                        disjunction,
                        &context.values,
                        &context.array_refs,
                        &context.memory,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `cases` disjunction: {message}"
                        ))
                    })?;
                    let Proposition::Or(left_disjunct, right_disjunct) = &lowered else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `cases` requires a disjunction, got {}",
                            describe_pure_fact(&lowered, &[], &[])
                        )));
                    };
                    if !pure_fact_is_available(&lowered, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `cases` requires its exact disjunction as an available fact: {}",
                            describe_pure_fact(&lowered, &[], &[])
                        )));
                    }
                    available.push(if *left {
                        left_disjunct.as_ref().clone()
                    } else {
                        right_disjunct.as_ref().clone()
                    });
                }
            }
        }
        if closed {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `{}` follows a goal-closing tactic",
                tactic_name(tactic)
            )));
        }

        match tactic {
            ProofTactic::Induct {
                parameter,
                hypothesis,
            } => {
                let Some(setup) = induction_setup else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unexpected induction certificate"
                    )));
                };
                if induction_active
                    || parameter != &setup.parameter
                    || hypothesis != &setup.hypothesis
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction certificate does not match its theorem setup"
                    )));
                }
                let Some(CValue::Int32(term)) = context.values.get(parameter) else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction parameter must have type int32"
                    )));
                };
                let nonnegative = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(term.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                );
                let assumptions = assumptions_from_propositions(&available);
                if !available.contains(&nonnegative)
                    && assumptions.derive_proposition(&nonnegative).is_none()
                    && !matches!(
                        simp_proposition(&nonnegative, &assumptions),
                        SimpProposition::True
                    )
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `induct({parameter})` requires a proof that `{parameter}` is nonnegative"
                    )));
                }
                induction_active = true;
                let hypothesis = pure_induction_hypothesis(
                    setup,
                    context,
                    predicate_environment,
                    click_function_environment,
                )?;
                if !available.contains(&hypothesis) {
                    available.push(hypothesis);
                }
            }
            ProofTactic::ApplyInduction {
                hypothesis,
                argument,
            } => {
                if !induction_active {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction hypothesis used before `induct`"
                    )));
                }
                apply_pure_induction_hypothesis(
                    induction_setup.expect("active induction has a setup"),
                    hypothesis,
                    argument,
                    None,
                    claim_label,
                    tactic_index,
                    &mut available,
                    context,
                    predicate_environment,
                    click_function_environment,
                )?;
            }
            ProofTactic::ApplyInductionUsing {
                hypothesis,
                argument,
                premises,
            } => {
                if !induction_active {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: induction hypothesis used before `induct`"
                    )));
                }
                apply_pure_induction_hypothesis(
                    induction_setup.expect("active induction has a setup"),
                    hypothesis,
                    argument,
                    Some(premises),
                    claim_label,
                    tactic_index,
                    &mut available,
                    context,
                    predicate_environment,
                    click_function_environment,
                )?;
            }
            ProofTactic::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: unknown predicate `{name}`"
                    )));
                }
                if !unfolded_predicates.contains(name) {
                    unfolded_predicates.push(name.clone());
                }
                available = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &available,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
                let assumptions = assumptions_from_propositions(&available);
                goal = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &goal,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
            }
            ProofTactic::UnfoldFunction(application) => {
                let definition = click_function_environment
                    .get(&application.name)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: unknown pure function `{}` in `unfold`",
                            application.name
                        ))
                    })?;
                let variable_types =
                    generics::concrete_variable_types(&context.values, &BTreeMap::new());
                let definition = generics::instantiate_function_for_surface_call_with_variables(
                    definition,
                    &application.arguments,
                    &variable_types,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
                if application.arguments.len() != definition.parameters().len() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: function `{}` expects {} argument(s), got {}",
                        definition.name(),
                        definition.parameters().len(),
                        application.arguments.len()
                    )));
                }
                let substitutions = definition
                    .parameters()
                    .iter()
                    .zip(&application.arguments)
                    .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                    .collect::<BTreeMap<_, _>>();
                let surface_body =
                    substitute_contract_expression(definition.body(), &substitutions).map_err(
                        |message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not instantiate function `{}` for `unfold`: {message}",
                                application.name
                            ))
                        },
                    )?;
                let surface_equality = ClickProposition::Comparison {
                    left: ContractExpression::Call {
                        name: application.name.clone(),
                        arguments: application.arguments.clone(),
                    },
                    operator: ComparisonOperator::Equal,
                    right: surface_body.clone(),
                };
                let equality = lower_pure_theorem_proposition_with_opaque_calls(
                    claim_label,
                    &surface_equality,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                    &BTreeSet::from([application.name.clone()]),
                )
                .map_err(ClickError::new)?;
                if !available.contains(&equality) {
                    available.push(equality);
                }

                let Some(current_surface_goal) = surface_goal.as_ref() else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: function `unfold` lost the theorem's surface goal"
                    )));
                };
                let surface_equality = ClickProposition::Comparison {
                    left: ContractExpression::Call {
                        name: application.name.clone(),
                        arguments: application.arguments.clone(),
                    },
                    operator: ComparisonOperator::Equal,
                    right: surface_body,
                };
                if let Some(next_surface_goal) = rewrite_click_proposition_by_surface_equality(
                    current_surface_goal,
                    &surface_equality,
                ) {
                    surface_goal = Some(next_surface_goal.clone());
                    let assumptions = assumptions_from_propositions(&available);
                    let values = context.values.clone();
                    let mut opaque_calls = BTreeSet::new();
                    crate::surface::validation::collect_click_function_calls_in_proposition(
                        &next_surface_goal,
                        &mut opaque_calls,
                    );
                    goal = lower_fixed_state_proposition_through_kernel_with_opaque_calls_and_integer_values(
                        &next_surface_goal,
                        &assumptions,
                        &values,
                        &context.array_refs,
                        &context.integer_values,
                        &state,
                        &state,
                        None,
                        &RecordedSnapshots::new(),
                        predicate_environment,
                        click_function_environment,
                        &opaque_calls,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not refresh the goal after function `unfold`: {message}"
                        ))
                    })?;
                }
            }
            ProofTactic::Have(have) => {
                let proposition = lower_pure_theorem_proposition(
                    claim_label,
                    &have.proposition,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not lower `have` proposition: {message}"
                    ))
                })?;
                let SourceProof::Script(have_tactics) = &have.proof else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: expanded `have` requires an explicit simple proof"
                    )));
                };
                let certificate = ProofCertificate::from_proof_tactics(have_tactics).map_err(
                    |error| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: invalid `have` certificate: {error:?}"
                        ))
                    },
                )?;
                validate_pure_theorem_certificate(
                    claim_label,
                    &available,
                    &proposition,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    context,
                    &certificate,
                    None,
                )?;
                if !available.contains(&proposition) {
                    available.push(proposition);
                }
            }
            ProofTactic::ApplyTheorem(application) => {
                available = apply_theorem_applications_to_available(
                    theorem_environment,
                    &[(tactic_index, application.clone())],
                    claim_label,
                    None,
                    available,
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => {
                let explicit_premises = premises
                    .iter()
                    .map(|premise| {
                        lower_pure_theorem_proposition_with_integer_values(
                            claim_label,
                            premise,
                            &context.values,
                            &context.integer_values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available) {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `apply using` requires an unavailable exact premise: {premise:?}"
                        )));
                    }
                }
                let mut applied = apply_theorem_applications_to_available_with_lowering_context(
                    theorem_environment,
                    &[(tactic_index, application.clone())],
                    claim_label,
                    None,
                    explicit_premises,
                    Some(&available),
                    &application_context,
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                )?;
                for fact in available {
                    if !applied.contains(&fact) {
                        applied.push(fact);
                    }
                }
                available = applied;
            }
            ProofTactic::InstantiateUsing {
                quantified: surface_quantified,
                argument,
                premises: surface_premises,
            } => {
                let explicit_premises = surface_premises
                    .iter()
                    .map(|premise| {
                        lower_pure_theorem_proposition(
                            claim_label,
                            premise,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `instantiate using` premise: {message}"
                        ))
                    })?;
                for premise in &explicit_premises {
                    if !exact_fact_is_available(premise, &available)
                        && quantified_equivalent_available_fact(premise, &available).is_none()
                    {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: `instantiate using` requires an exact available premise"
                        )));
                    }
                }

                let lowered_quantified = lower_pure_theorem_proposition(
                    claim_label,
                    surface_quantified,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not lower `instantiate` quantified fact: {message}"
                    ))
                })?;
                let quantified_fact = if exact_fact_is_available(&lowered_quantified, &available) {
                    lowered_quantified
                } else if let Some(matched) =
                    quantified_equivalent_available_fact(&lowered_quantified, &available)
                {
                    matched
                } else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `instantiate` quantified fact is not exactly available: {}",
                        describe_click_proposition(surface_quantified)
                    )));
                };

                let assumptions = assumptions_from_propositions(&available);
                let mut active_functions = BTreeSet::new();
                let state = CState::new().with_memory(context.memory.clone());
                let argument_value = evaluate_contract_expression_with_environment(
                    &context.values,
                    &context.array_refs,
                    &state,
                    &state,
                    None,
                    &assumptions,
                    argument,
                    predicate_environment,
                    click_function_environment,
                    &recorded_snapshots,
                    &mut active_functions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not evaluate `instantiate` argument: {message}"
                    ))
                })?;
                let CValue::Int32(argument_term) = argument_value else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `instantiate` argument did not evaluate to int32"
                    )));
                };

                let conclusion = check_forall_int32_instantiation(
                    &quantified_fact,
                    argument_term,
                    &explicit_premises,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `instantiate` failed: {message}"
                    ))
                })?;
                if !available.contains(&conclusion) {
                    available.push(conclusion);
                }
            }
            ProofTactic::Assumption => {
                if !available.contains(&goal)
                    && exactly_available_fact(&goal, &available).is_none()
                    && quantified_equivalent_available_fact(&goal, &available).is_none()
                {
                    return Err(ClickError::new(format!(
                        "`assumption` failed for `{claim_label}`: {}",
                        describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                    )));
                }
                closed = true;
            }
            ProofTactic::Extract(surface_proposition) => {
                let mut proposition = lower_pure_theorem_proposition(
                    claim_label,
                    surface_proposition,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`extract` failed for `{claim_label}`: could not lower proposition: {message}"
                    ))
                })?;
                proposition = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                    &proposition,
                    &assumptions_from_propositions(&available),
                )
                .map_err(|message| {
                    ClickError::new(format!("`extract` failed for `{claim_label}`: {message}"))
                })?;
                let extraction_assumptions = assumptions_from_propositions(&available);
                if !exact_proper_conjunct_is_available(&proposition, &available)
                    && !discharged_implication_consequent_is_available(&proposition, &available)
                    && !extraction_assumptions
                        .contains_algebraic_constructor_field_equality(&proposition)
                {
                    return Err(ClickError::new(format!(
                        "`extract` failed for `{claim_label}`: proposition is not a proper conjunct, a discharged implication consequent, or a field equality of an exact same-constructor equality: {}",
                        describe_pure_fact(&proposition, &[], &[])
                    )));
                }
                if !available.contains(&proposition) {
                    available.push(proposition);
                }
            }
            ProofTactic::Normalize => {
                if !normalizes_context_free(&goal) {
                    return Err(ClickError::new(format!(
                        "`normalize` failed for `{claim_label}`: goal did not normalize to true: {}",
                        describe_pure_fact(&goal, &[], &[])
                    )));
                }
                closed = true;
            }
            ProofTactic::NormalizeUsing(surface_premises) => {
                let premises = surface_premises
                    .iter()
                    .map(|premise| {
                        lower_pure_theorem_proposition(
                            claim_label,
                            premise,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(ClickError::new)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                    &goal,
                    &premises,
                    &crate::kernel::proof::ProofFacts::from_ordered(&available),
                )
                .map_err(|error| {
                    ClickError::new(format!(
                        "`normalize using` failed for `{claim_label}`: {error:?}"
                    ))
                })?;
                closed = true;
            }
            ProofTactic::ArithmeticUsing(surface_premises) => {
                let premises = surface_premises
                    .iter()
                    .enumerate()
                    .map(|(premise_index, premise)| {
                        let lowered = lower_pure_theorem_proposition(
                            claim_label,
                            premise,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: could not lower `arithmetic using` premise {premise_index}: {message}"
                            ))
                        })?;
                        if !exact_fact_is_available(&lowered, &available) {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {tactic_index}: `arithmetic using` premise {premise_index} is not exactly available"
                            )));
                        }
                        Ok(lowered)
                    })
                    .collect::<Result<Vec<_>, ClickError>>()?;
                crate::kernel::proof::fact_reasoning::check_signed_affine_arithmetic(
                    &goal, &premises,
                )
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `arithmetic` failed: {error:?}"
                    ))
                })?;
                closed = true;
            }
            ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Enumerate
            | ProofTactic::Contradiction(_) => {
                let contradiction_fact = match tactic {
                    ProofTactic::Contradiction(surface_fact) => Some(
                        lower_pure_theorem_proposition(
                            claim_label,
                            surface_fact,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                        .map_err(|message| {
                            ClickError::new(format!(
                                "`contradiction` failed for `{claim_label}`: could not lower fact: {message}"
                            ))
                        })?,
                    ),
                    _ => None,
                };
                closed = apply_logical_goal_tactic(
                    tactic,
                    &mut goal,
                    &mut available,
                    contradiction_fact,
                )
                .map_err(|message| {
                    ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                })?;
            }
            ProofTactic::SimpUsing(simp) => {
                let target = goal.clone();
                let premises = simp
                    .premises
                    .iter()
                    .map(|premise| {
                        lower_pure_theorem_proposition(
                            claim_label,
                            premise,
                            &context.values,
                            &context.array_refs,
                            &context.memory,
                            predicate_environment,
                            click_function_environment,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` tactic {tactic_index}: could not lower `simp` premise: {message}"
                        ))
                    })?;
                plan_restricted_simp_goal(&target, premises, &goal, &available).map_err(
                    |message| {
                        ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {message}"))
                    },
                )?;
                closed = true;
            }
            ProofTactic::Rewrite(surface_equality) => {
                let mut equality = lower_pure_theorem_proposition(
                    claim_label,
                    surface_equality,
                    &context.values,
                    &context.array_refs,
                    &context.memory,
                    predicate_environment,
                    click_function_environment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`rewrite` failed for `{claim_label}`: could not lower equality: {message}"
                    ))
                })?;
                let assumptions = assumptions_from_propositions(&available);
                equality = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    &unfolded_predicates,
                    &equality,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!("`rewrite` failed for `{claim_label}`: {message}"))
                })?;
                goal = rewrite_proposition_by_exact_equality(&goal, &equality, &available)
                    .map_err(|message| {
                        ClickError::new(format!("`rewrite` failed for `{claim_label}`: {message}"))
                    })?;
            }
            ProofTactic::Simp => {
                let assumptions = assumptions_from_propositions(&available);
                if assumptions.derive_proposition(&goal).is_some() {
                    closed = true;
                    continue;
                }
                match simp_proposition(&goal, &assumptions) {
                    SimpProposition::True => closed = true,
                    _ => {
                        return Err(ClickError::new(format!(
                            "`simp` failed for `{claim_label}`: simplified proposition was not true: {}\n  {}",
                            describe_pure_fact(&goal, &[], &[]),
                            describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
                        )));
                    }
                }
            }
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` pure tactic {tactic_index}: `{}` is not available in a pure proof",
                    tactic_name(tactic)
                )));
            }
        }
    }

    if closed || available.contains(&goal) {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "tactics failed for `{claim_label}`: {}",
            describe_missing_pure_fact(&goal, &available, &[], &[], &[], &[])
        )))
    }
}
