use super::*;
use crate::kernel::AlgebraicValueType;
use crate::kernel::c_function_contract_refinement_obligations;

const STRUCTURAL_INDUCTION_VARIABLE_BASE: u64 = 1 << 60;

mod execution_theorems;
use execution_theorems::verify_execution_theorem;

#[cfg(test)]
thread_local! {
    /// Names of the theorem definitions this thread has proved, in order, so
    /// tests can check which dependencies a verification re-proves.
    pub(in crate::surface) static PROVED_THEOREMS: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Proves `theorem_definitions` in order. Each proof may apply `dependencies`
/// and the definitions before it. Dependencies are declarations proved
/// elsewhere, such as the standard library, and are not re-proved here.
pub(in crate::surface) fn verify_theorem_definitions(
    dependencies: &[TheoremDefinition],
    theorem_definitions: &[TheoremDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
    resource_environment: &ResourceEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = TheoremEnvironment::new(dependencies);
    for theorem in theorem_definitions {
        #[cfg(test)]
        PROVED_THEOREMS.with(|proved| proved.borrow_mut().push(theorem.name().to_string()));
        if theorem.executes.is_some() {
            verified.push(verify_execution_theorem(
                theorem,
                predicate_environment,
                click_function_environment,
                &theorem_environment,
                function_environment,
                resource_environment,
                function_source_registry.clone(),
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
    /// The theorem's parameter list as this application spells it: either
    /// every parameter in declaration order, or the inducted position alone.
    pub(super) arguments: Vec<ContractExpression>,
    pub(super) surface_premises: Vec<ClickProposition>,
    pub(super) kernel_premises: Vec<Proposition>,
    pub(super) implication: Proposition,
    pub(super) conclusion: Proposition,
}

#[derive(Clone, Debug)]
pub(super) struct PureStructuralInductionBranchSetup {
    pub(super) hypothesis: String,
    /// The inducted parameter's position in the theorem's declaration order.
    /// The argument there must descend; every other position may name any
    /// well-typed term.
    pub(super) parameter_index: usize,
    /// This arm's bindings of the inducted datatype: the only values the
    /// inducted position may name.
    pub(super) recursive_bindings: Vec<String>,
    pub(super) applications: Vec<PureStructuralInductionApplication>,
    pub(super) algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
}

/// The bare parameter or binding name an induction argument spells, when it
/// spells one rather than a compound term.
pub(super) fn induction_argument_name(argument: &ContractExpression) -> Option<&str> {
    match argument {
        ContractExpression::Binding(name)
        | ContractExpression::AlgebraicVariable { name, .. }
        | ContractExpression::CFragment(CExpression::Variable(name)) => Some(name),
        _ => None,
    }
}

/// The argument occupying the inducted position of one hypothesis
/// application. This is the only position that must descend; a one-argument
/// application spells that position alone.
pub(super) fn structural_induction_descent_argument(
    parameter_index: usize,
    arguments: &[ContractExpression],
) -> Option<&ContractExpression> {
    if arguments.len() == 1 {
        arguments.first()
    } else {
        arguments.get(parameter_index)
    }
}

/// Checks the descent of one hypothesis application: the inducted position
/// names a field this arm's pattern bound, of the datatype being inducted on.
/// This is a bounded structural test against the arm's own binding list, not
/// a search through the proof state.
pub(super) fn structural_induction_descends(
    setup: &PureStructuralInductionBranchSetup,
    arguments: &[ContractExpression],
) -> bool {
    structural_induction_descent_argument(setup.parameter_index, arguments)
        .and_then(induction_argument_name)
        .is_some_and(|name| {
            setup
                .recursive_bindings
                .iter()
                .any(|binding| binding == name)
        })
}

/// The substitution one `ih(...)` application makes in the theorem's own
/// clauses.
///
/// A proof may spell every parameter in declaration order, which is how the
/// hypothesis is instantiated at parameters other than the inducted one, or
/// spell the inducted position alone, which leaves every other parameter at
/// its current value. A position that names its own parameter substitutes
/// nothing, so the theorem's own elaboration of that parameter is retained.
fn structural_induction_hypothesis_substitution(
    theorem: &TheoremDefinition,
    parameter: &str,
    hypothesis: &str,
    arguments: &[ContractExpression],
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    let parameters = theorem.parameters();
    if arguments.len() == 1 {
        return Ok(BTreeMap::from([(
            parameter.to_string(),
            arguments[0].clone(),
        )]));
    }
    if arguments.len() != parameters.len() {
        return Err(ClickError::new(format!(
            "induction hypothesis `{hypothesis}` expects {} argument(s) in declaration order, or `{parameter}` alone, got {}",
            parameters.len(),
            arguments.len()
        )));
    }
    let mut substitution = BTreeMap::new();
    for (definition, argument) in parameters.iter().zip(arguments) {
        if induction_argument_name(argument) == Some(definition.name()) {
            continue;
        }
        substitution.insert(definition.name().to_string(), argument.clone());
    }
    Ok(substitution)
}

/// Collects the hypothesis parameter lists an arm's script spells, in order
/// and without repetition. Each one becomes exactly one instantiated
/// hypothesis premise, so an arm costs one instance per written application
/// rather than an enumeration of candidate instances.
fn collect_structural_induction_arguments(
    tactics: &[ProofTactic],
    hypothesis: &str,
    collected: &mut Vec<Vec<ContractExpression>>,
) {
    for tactic in tactics {
        match tactic {
            ProofTactic::ApplyTheorem(application)
            | ProofTactic::ApplyTheoremUsing { application, .. }
                if application.name == hypothesis =>
            {
                if !collected.contains(&application.arguments) {
                    collected.push(application.arguments.clone());
                }
            }
            ProofTactic::If(proof_if) => {
                collect_structural_induction_arguments(
                    &proof_if.then_tactics,
                    hypothesis,
                    collected,
                );
                collect_structural_induction_arguments(
                    &proof_if.else_tactics,
                    hypothesis,
                    collected,
                );
            }
            ProofTactic::Both(both) => {
                collect_structural_induction_arguments(&both.left_tactics, hypothesis, collected);
                collect_structural_induction_arguments(&both.right_tactics, hypothesis, collected);
            }
            ProofTactic::Cases(proof_cases) => {
                collect_structural_induction_arguments(
                    &proof_cases.left_tactics,
                    hypothesis,
                    collected,
                );
                collect_structural_induction_arguments(
                    &proof_cases.right_tactics,
                    hypothesis,
                    collected,
                );
            }
            _ => {}
        }
    }
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
                    // Measure induction quantifies one `int32` variable, so
                    // its hypothesis names only the replacement measure.
                    let [argument] = application.arguments.as_slice() else {
                        return Err(ClickError::new(format!(
                            "induction hypothesis `{hypothesis}` expects one argument"
                        )));
                    };
                    Ok(ProofTactic::ApplyInduction {
                        hypothesis: hypothesis.to_string(),
                        arguments: vec![argument.clone()],
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
                        arguments: vec![argument.clone()],
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
            CType::VoidPointerPointer => C0Type::VoidPointerPointer,
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
                // Every written application was instantiated when the arm's
                // premises were built, so this is a lookup, not a search.
                let Some(selected) = setup
                    .applications
                    .iter()
                    .find(|candidate| candidate.arguments == application.arguments)
                else {
                    return Err(ClickError::new(
                        "structural induction hypothesis expects an immediate recursive field",
                    ));
                };
                Ok(ProofTactic::ApplyInductionUsing {
                    hypothesis: setup.hypothesis.clone(),
                    arguments: application.arguments.clone(),
                    premises: selected.surface_premises.clone(),
                })
            }
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } if application.name == setup.hypothesis => Ok(ProofTactic::ApplyInductionUsing {
                hypothesis: setup.hypothesis.clone(),
                arguments: application.arguments.clone(),
                premises: premises.clone(),
            }),
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
) -> Result<
    (
        ProofCertificate,
        Vec<crate::kernel::proof::CheckedProposition>,
    ),
    ClickError,
> {
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
    let mut completions = Vec::new();
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
        let recursive_bindings = arm
            .bindings
            .iter()
            .zip(&variant.fields)
            .filter(|(_, field_type)| *field_type == &root_value_type)
            .map(|(binding, _)| binding.clone())
            .collect::<Vec<_>>();
        // Every immediate recursive field keeps its hypothesis at the
        // theorem's current parameters, and the arm's script adds one
        // instance for each parameter list it spells.
        let mut application_arguments = recursive_bindings
            .iter()
            .map(|binding| vec![ContractExpression::Binding(binding.clone())])
            .collect::<Vec<_>>();
        collect_structural_induction_arguments(
            &arm.tactics,
            hypothesis,
            &mut application_arguments,
        );
        let mut applications = Vec::new();
        for arguments in application_arguments {
            let child_substitution = structural_induction_hypothesis_substitution(
                theorem, parameter, hypothesis, &arguments,
            )?;
            let descends = structural_induction_descent_argument(parameter_index, &arguments)
                .and_then(induction_argument_name)
                .is_some_and(|name| recursive_bindings.iter().any(|binding| binding == name));
            if !descends {
                return Err(ClickError::new(
                    "structural induction hypothesis expects an immediate recursive field",
                ));
            }
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
            // Two spellings of the same instance, such as `ih(tail)` and the
            // complete list that repeats the other parameters, state one
            // premise.
            if !branch_requires.contains(&implication) {
                branch_requires.push(implication.clone());
            }
            applications.push(PureStructuralInductionApplication {
                arguments,
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
            parameter_index,
            recursive_bindings,
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
        let mut search = super::attempt::search_scope("pure structural induction arm");
        let attempted = match root.try_authoritative_linear_script(&prepared) {
            Ok(attempted) => attempted,
            Err(error) => return Err(error.with_search_failures(search.finish())),
        };
        let Some(proof) = attempted else {
            let error = root.step_error(format!(
                "`{claim_label}` structural induction arm `{}::{}` did not close its goal",
                arm.type_name, arm.variant
            ));
            return Err(error.with_search_failures(search.finish()));
        };
        search.succeed();
        completions.push(proof.completed_proposition()?);
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
    let certificate = ProofCertificate::from_proof_tactics(&[ProofTactic::StructuralInduct {
        parameter: parameter.clone(),
        hypothesis: hypothesis.clone(),
        arms: checked_arms,
    }])
    .map_err(|error| {
        ClickError::new(format!(
            "structural induction for `{claim_label}` produced an invalid certificate: {error:?}"
        ))
    })?;
    Ok((certificate, completions))
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

/// Lowers imported or otherwise unselected theorem statements into scoped
/// certification assumptions. Proof bodies are intentionally ignored.
pub(in crate::surface) fn assumed_theorem_certification_authorities(
    theorems: &[TheoremDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<(String, Proposition, CVerifiedPureTheorem)>, ClickError> {
    let mut assumptions = Vec::new();
    for theorem in theorems {
        if !theorem.type_parameters().is_empty()
            || !theorem
                .parameters()
                .iter()
                .all(|parameter| parameter.click_type() == &ClickType::C(C0Type::Int32))
        {
            continue;
        }
        let context =
            pure_theorem_context(theorem, predicate_environment, click_function_environment)?;
        let variables = theorem
            .parameters()
            .iter()
            .map(|parameter| match context.values.get(parameter.name()) {
                Some(CValue::Int32(Bitvector32Term::Variable(variable))) => Some(*variable),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .expect("the int32 parameter filter creates int32 variables");
        for ensure in theorem.ensures() {
            let Ensure::Proposition(surface_goal) = ensure.ensure() else {
                continue;
            };
            let lowering_assumptions = assumptions_from_propositions(&context.requires);
            let (conclusion, _) = lower_pure_theorem_proposition_recording_introductions(
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
                    "could not lower assumed theorem `{}` conclusion: {message}",
                    theorem.name()
                ))
            })?;
            let Some(authority) = assume_universally_quantified_pure_implication(
                context.requires.clone(),
                conclusion.clone(),
                variables.clone(),
            ) else {
                continue;
            };
            let fact = variables.iter().rev().fold(
                context
                    .requires
                    .iter()
                    .rev()
                    .fold(conclusion, |body, requirement| {
                        Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
                    }),
                |body, variable| Proposition::ForAll {
                    var: *variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                },
            );
            assumptions.push((theorem.name().to_string(), fact, authority));
        }
    }
    Ok(assumptions)
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
                C0Type::VoidPointer | C0Type::VoidPointerPointer => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            1,
                        ),
                    },
                    c_type.to_kernel_type(),
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

    let (proof_kind, certificate, checked_completion) = match ensure_clause.proof() {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
            let (certificate, completion) = check_direct_pure_goal_with_proof(
                claim_label,
                context,
                surface_goal,
                &goal,
                &goal_introductions,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            )?;
            let kind = if matches!(
                ensure_clause.proof(),
                SourceProof::Tactic(SmartTactic::Simp)
            ) {
                ProofKind::Simp
            } else {
                ProofKind::Pure
            };
            (
                kind,
                certificate,
                TheoremProofCompletion::Proposition(completion),
            )
        }
        SourceProof::Script(tactics) => {
            if tactics.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` has an empty explicit proof script"
                )));
            }
            if matches!(tactics.first(), Some(ProofTactic::StructuralInduct { .. })) {
                let (certificate, completions) = check_pure_structural_induction(
                    theorem,
                    claim_label,
                    context,
                    surface_goal,
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                    tactics,
                )?;
                (
                    ProofKind::TacticScript,
                    certificate,
                    TheoremProofCompletion::StructuralInduction(completions),
                )
            } else {
                let (tactics, setup) =
                    prepare_pure_induction_tactics(theorem, surface_goal, tactics)?;
                let (certificate, completion) = check_pure_script_with_proof(
                    claim_label,
                    context,
                    surface_goal,
                    &goal,
                    &goal_introductions,
                    &tactics,
                    setup.as_ref(),
                    predicate_environment,
                    click_function_environment,
                    theorem_environment,
                )?;
                (
                    ProofKind::TacticScript,
                    certificate,
                    TheoremProofCompletion::Proposition(completion),
                )
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
    let kernel_authority = match (kernel_variables, &checked_completion) {
        (Some(variables), TheoremProofCompletion::Proposition(completion)) => {
            certificate_int32_rewrites(
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
                    completion,
                )
            })
            .or_else(|| {
                prove_universally_quantified_pure_implication(
                    context.requires.clone(),
                    goal.clone(),
                    variables,
                    completion,
                )
            })
        }
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
        checked_completion: Some(checked_completion),
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
    let mut search = super::attempt::search_scope("contract refinement");
    let attempted = match root.try_authoritative_linear_script(proof_tactics) {
        Ok(attempted) => attempted,
        Err(error) => {
            return Err(error
                .with_context(refinement_failure().message())
                .with_search_failures(search.finish()));
        }
    };
    let proof = match attempted {
        Some(proof) => {
            search.succeed();
            proof
        }
        None => return Err(refinement_failure().with_search_failures(search.finish())),
    };
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
        checked_completion: None,
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
) -> Result<(ProofCertificate, crate::kernel::proof::CheckedProposition), ClickError> {
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
    let mut search = super::attempt::search_scope("pure theorem simp");
    let result = match root.try_simp_closure() {
        Ok(result) => result,
        Err(error) => return Err(error.with_search_failures(search.finish())),
    };
    let Some(proof) = result else {
        return Err(root.simp_failure().with_search_failures(search.finish()));
    };
    search.succeed();
    Ok((
        proof.completed_certificate()?,
        proof.completed_proposition()?,
    ))
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

fn is_nat_integer_law_name(name: &str) -> bool {
    matches!(
        name,
        "nat_integer_zero"
            | "nat_integer_succ"
            | "nat_integer_nonnegative"
            | "nat_integer_round_trip"
            | "integer_nat_round_trip"
            | "integer_to_nat_zero"
    )
}

pub(in crate::surface) fn is_kernel_standard_theorem_name(name: &str) -> bool {
    integer_round_trip_destination(name).is_some()
        || is_nat_integer_law_name(name)
        || matches!(
            name,
            "int32_add_defined_by_integer_bounds"
                | "int32_add_to_integer"
                | "int32_less_equal_to_integer"
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
        "nat_integer_zero" | "integer_to_nat_zero" => (0, 0),
        "nat_integer_succ" | "nat_integer_nonnegative" | "nat_integer_round_trip" => (1, 0),
        "integer_nat_round_trip" => (1, 1),
        name if integer_round_trip_destination(name).is_some() => (1, 2),
        "int32_add_defined_by_integer_bounds" => (2, 2),
        "int32_add_to_integer" | "int32_less_equal_to_integer" | "int32_subtract_to_integer" => {
            (2, 1)
        }
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
    let axiom = if is_nat_integer_law_name(theorem.name()) {
        let proposition = context
            .requires
            .iter()
            .rev()
            .fold(goal.clone(), |body, requirement| {
                Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
            });
        crate::kernel::check_nat_integer_law(theorem.name(), &proposition).ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` declaration does not match its kernel Nat conversion law"
            ))
        })?
    } else if let Some(destination) = integer_round_trip_destination(theorem.name()) {
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
            "int32_less_equal_to_integer" => {
                crate::kernel::prove_int32_less_equal_to_integer(value, int32_parameter(1)?)
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
        checked_completion: None,
    })
}

/// Run source once through the checked operation driver and retain its result.
#[allow(clippy::too_many_arguments)]
fn check_pure_script_with_proof(
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    goal_introductions: &crate::kernel::LoweringIntroductions,
    tactics: &[ProofTactic],
    induction_setup: Option<&PureInductionSetup>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<(ProofCertificate, crate::kernel::proof::CheckedProposition), ClickError> {
    let root = match induction_setup {
        Some(setup) => Proof::for_pure_surface_goal_with_induction(
            claim_label,
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            context,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            setup.clone(),
        ),
        None => Proof::for_pure_surface_goal(
            claim_label,
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            context,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        ),
    }
    .with_recorded_goal_introductions(Some(goal_introductions.clone()));
    let mut search = super::attempt::search_scope("pure theorem script");
    let mut declined = None;
    let checked = match root.try_authoritative_linear_script_reporting(tactics, &mut declined) {
        Ok(checked) => checked,
        Err(error) => return Err(error.with_search_failures(search.finish())),
    };
    let Some(proof) = checked else {
        let detail = match declined {
            Some(super::smart_closures::LinearScriptDecline::Shape) => {
                "contains an unsupported operation or control-flow shape".to_string()
            }
            Some(super::smart_closures::LinearScriptDecline::Step(index)) => format!(
                "could not complete tactic {} (`{}`)",
                index + 1,
                tactic_name(&tactics[index])
            ),
            None => "ended with its goal still open".to_string(),
        };
        return Err(root
            .step_error(format!("checked pure script for `{claim_label}` {detail}"))
            .with_search_failures(search.finish()));
    };
    search.succeed();
    Ok((
        proof.completed_certificate()?,
        proof.completed_proposition()?,
    ))
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
            | ContractExpression::ArrayIndex { .. }
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

pub(super) fn induction_application_surface_premises(
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
        BTreeMap::new(),
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
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordinary_pure_scripts_retain_completion_without_compatibility() {
        for body in [
            "normalize();",
            "simp();",
            "have x == x by { simp(); } assumption();",
            "if x == 0 { normalize(); } else { normalize(); }",
        ] {
            let source = format!("theorem ordinary(x: int32) {{ ensures x == x by {{ {body} }} }}");
            let (result, events) =
                crate::instrumentation::collect(|| verify_instantiation_theorem(&source));
            let verified = result.unwrap();
            assert!(
                matches!(&verified.checked_completion, Some(TheoremProofCompletion::Proposition(completion)) if completion.proposition() == &verified.conclusion)
            );
            assert!(verified.kernel_authority.is_some());
            assert!(!verified.proof_certificate().unwrap().steps().is_empty());
            assert!(!events.iter().any(|event| matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "generated certificate validation" || name == "surface certificate construction"
            )));
        }
        let error = verify_instantiation_theorem(
            "theorem bad(x: int32) { ensures x == 0 by { normalize(); simp(); } }",
        )
        .unwrap_err();
        assert!(
            error
                .message()
                .contains("`normalize` goal did not normalize"),
            "{}",
            error.message()
        );
        let error = verify_instantiation_theorem(
            "theorem unsupported() { ensures 0 == 0 by { execute(); } }",
        )
        .unwrap_err();
        assert!(error.message().contains("execute"), "{}", error.message());
    }

    #[test]
    fn ordinary_pure_fact_producers_preserve_written_suffixes() {
        let source = r#"
            theorem identity(x: int32) { requires x == 0; ensures x == 0 by { assumption(); } }
            theorem application(x: int32) {
                requires x == 0;
                ensures x == 0 by { apply(identity(x)); rewrite(x == 0); normalize(); }
            }
            theorem extraction(x: int32) {
                requires x == 0 and x <= 1;
                ensures x == 0 by { extract(x == 0); rewrite(x == 0); normalize(); }
            }
        "#;
        let verified = crate::surface::verify_click_theorems(source).unwrap();
        for theorem in &verified[1..] {
            let certificate = theorem.proof_certificate().unwrap();
            assert!(matches!(
                certificate.steps().first(),
                Some(ProofStep::Have { .. })
            ));
            assert!(theorem.kernel_authority.is_some());
        }
        for label in ["application.ensures_0", "extraction.ensures_0"] {
            let expanded =
                crate::surface::expand_c0_claim_source_by_label(source, &[], label).unwrap();
            crate::surface::verify_c0_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    fn ordinary_pure_numeric_induction_expands_and_reverifies() {
        for fixture in [
            include_str!("../../../mdtests/pure_induction_countdown.md"),
            include_str!("../../../mdtests/pure_induction_two_step.md"),
            include_str!("../../../mdtests/pure_induction_mutual_conjunction.md"),
        ] {
            let source = fixture
                .split_once("```click\n")
                .unwrap()
                .1
                .split_once("\n```")
                .unwrap()
                .0;
            let (result, events) =
                crate::instrumentation::collect(|| verify_instantiation_theorem(source));
            let verified = result.unwrap();
            assert!(matches!(
                verified.checked_completion,
                Some(TheoremProofCompletion::Proposition(_))
            ));
            assert!(verified.kernel_authority.is_some());
            assert!(!events.iter().any(|event| matches!(event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "generated certificate validation" || name == "surface certificate construction"
            )));
            let label = format!("{}.ensures_0", verified.theorem_definition.name());
            crate::surface::verify_c0_sources(source, &[]).unwrap();
            let expanded =
                crate::surface::expand_c0_claim_source_by_label(source, &[], &label).unwrap();
            crate::surface::verify_c0_sources(&expanded, &[]).unwrap();
            assert_eq!(
                expanded,
                crate::surface::expand_c0_claim_source_by_label(&expanded, &[], &label).unwrap()
            );
        }
    }

    #[test]
    fn ordinary_pure_structural_induction_retains_arm_evidence() {
        let source = r#"
            spec enum TestNat { Zero, Succ(TestNat), }
            theorem reflexive(n: TestNat) {
                ensures n == n by {
                    induct(n) as ih {
                        TestNat::Zero => { normalize(); }
                        TestNat::Succ(tail) => { normalize(); }
                    }
                }
            }
        "#;
        let verified = crate::surface::verify_click_theorems(source)
            .unwrap()
            .remove(0);
        assert!(verified.kernel_authority.is_none());
        assert!(
            matches!(&verified.checked_completion, Some(TheoremProofCompletion::StructuralInduction(arms)) if arms.len() == 2)
        );
        assert!(
            matches!(verified.proof_certificate().unwrap().steps(), [ProofStep::StructuralInduct { arms, .. }] if arms.len() == 2)
        );
    }

    #[test]
    fn ordinary_pure_compatibility_entry_points_stay_removed() {
        let production = include_str!("pure_theorems.rs")
            .split("#[cfg(test)]\nmod tests")
            .next()
            .unwrap();
        for name in [
            "prove_pure_theorem_script",
            "prove_pure_theorem_tactics",
            "prove_pure_theorem_goal",
            "validate_pure_theorem_certificate",
            "pure_theorem_surface_certificate",
            "proof_supports_pure_certificate",
        ] {
            assert!(
                !production.contains(name),
                "removed pure authority returned: {name}"
            );
        }
    }

    const INSTANTIATE_BOUND: &str = r#"
        theorem instantiate_bound(x: int32, limit: int32, upper: int32) {
            requires forall (k: int32) {
                0 <= k and k < limit implies k <= upper
            };
            requires 0 <= x;
            requires x < limit;
            ensures x <= upper by {
                instantiate(forall (k: int32) {
                    0 <= k and k < limit implies k <= upper
                }, x) using { 0 <= x; x < limit; }
                assumption();
            }
        }
    "#;

    fn verify_instantiation_theorem(source: &str) -> Result<VerifiedPureTheorem, ClickError> {
        let file = crate::surface::parse(source)?;
        let predicates = PredicateEnvironment::new(file.predicate_definitions());
        let functions = ClickFunctionEnvironment::new(file.click_function_definitions());
        let mut verified = verify_concrete_theorem_definition(
            &file.theorem_definitions()[0],
            &predicates,
            &functions,
            &TheoremEnvironment::new(&[]),
            None,
        )?;
        Ok(verified.remove(0))
    }

    #[test]
    fn pure_instantiate_retains_checked_authority_without_recertification() {
        let (result, events) =
            crate::instrumentation::collect(|| verify_instantiation_theorem(INSTANTIATE_BOUND));
        let verified = result.expect("pure instantiation must produce checked authority");
        assert!(verified.kernel_authority.is_some());
        assert!(matches!(
            verified.proof.as_ref().unwrap().steps(),
            [ProofStep::InstantiateUsing { .. }, ProofStep::Assumption]
        ));
        assert!(!events.iter().any(|event| matches!(event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "generated certificate validation" || name == "surface certificate construction"
        )), "ordinary instantiation must retain the checked result: {events:?}");
    }

    #[test]
    fn pure_instantiate_rejects_omitted_guard_and_preserves_checked_error() {
        let missing =
            INSTANTIATE_BOUND.replace("using { 0 <= x; x < limit; }", "using { 0 <= x; }");
        let error = verify_instantiation_theorem(&missing)
            .expect_err("ambient guards cannot fill a missing citation");
        assert!(
            error
                .message()
                .contains("does not follow from the listed evidence"),
            "{}",
            error.message()
        );
        assert!(
            !error.message().contains("round-trip"),
            "{}",
            error.message()
        );
        let unavailable = INSTANTIATE_BOUND.replace("requires x < limit;", "");
        let error = verify_instantiation_theorem(&unavailable)
            .expect_err("a named guard must be available");
        assert!(
            error.message().contains("unavailable exact premise"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn pure_instantiate_preserves_an_unrelated_open_goal() {
        let open = INSTANTIATE_BOUND
            .replace("ensures x <= upper", "ensures x == upper")
            .replace("                assumption();", "");
        let error = verify_instantiation_theorem(&open)
            .expect_err("instantiation does not change the selected goal");
        assert!(
            error.message().contains("goal still open"),
            "{}",
            error.message()
        );
        let failed = INSTANTIATE_BOUND.replace("ensures x <= upper", "ensures x == upper");
        let error = verify_instantiation_theorem(&failed)
            .expect_err("the explicit closer must fail on the original goal");
        assert!(
            error.message().contains("assumption"),
            "{}",
            error.message()
        );
        assert!(
            !error.message().contains("round-trip"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn pure_instantiate_resolves_introduced_binders_and_nested_shadowing() {
        let source = r#"
            theorem shadowed(x: int32) {
                requires x == 0;
                requires forall (k: int32) { k <= 10 implies k <= 20 };
                ensures forall (x: int32) { x <= 10 implies x <= 20 } by {
                    intro(); intro();
                    have x <= 20 by {
                        instantiate(forall (x: int32) { x <= 10 implies x <= 20 }, x)
                            using { x <= 10; }
                        assumption();
                    }
                    assumption();
                }
            }
        "#;
        let verified = verify_instantiation_theorem(source)
            .expect("intro bindings must shadow theorem parameters");
        assert!(verified.kernel_authority.is_some());
        let invalid = source.replace("using { x <= 10; }", "using { x == 0; }");
        assert!(
            verify_instantiation_theorem(&invalid).is_err(),
            "the outer x cannot supply evidence for the introduced x"
        );
    }

    #[test]
    fn pure_instantiate_keeps_nested_universal_binders_distinct() {
        let source = r#"
            theorem nested() {
                requires forall (k: int32) { forall (k: int32) { k == k } };
                ensures forall (x: int32) { x == x } by {
                    instantiate(forall (k: int32) { forall (k: int32) { k == k } }, 0) using {}
                    assumption();
                }
            }
        "#;
        assert!(
            verify_instantiation_theorem(source)
                .unwrap()
                .kernel_authority
                .is_some()
        );
        let invalid = source.replace(
            "ensures forall (x: int32) { x == x }",
            "ensures forall (x: int32) { x == 0 }",
        );
        assert!(verify_instantiation_theorem(&invalid).is_err());
    }

    #[test]
    fn pure_instantiate_in_numeric_induction_retains_completion() {
        let source = INSTANTIATE_BOUND.replace("0 <= x", "x >= 0").replace(
            "ensures x <= upper by {",
            "ensures x <= upper by { induct(x) as ih;",
        );
        let (verified, events) =
            crate::instrumentation::collect(|| verify_instantiation_theorem(&source));
        assert!(verified.unwrap().kernel_authority.is_some());
        assert!(!events.iter().any(|event| matches!(event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "generated certificate validation"
        )));
    }

    #[test]
    fn pure_instantiate_shares_unrelated_facts_and_bindings() {
        let mut allocations = Vec::new();
        for size in [8usize, 16, 32, 64] {
            let parameters = (0..size)
                .map(|i| format!(", unused{i}: int32"))
                .collect::<String>();
            let requirements = (0..size)
                .map(|i| format!("requires unused{i} == {i};\n"))
                .collect::<String>();
            let source = INSTANTIATE_BOUND
                .replace("upper: int32)", &format!("upper: int32{parameters})"))
                .replace(
                    "requires 0 <= x;",
                    &format!("{requirements}requires 0 <= x;"),
                );
            let file = crate::surface::parse(&source).unwrap();
            let theorem = &file.theorem_definitions()[0];
            let predicates = PredicateEnvironment::new(&[]);
            let functions = ClickFunctionEnvironment::new(&[]);
            let theorems = TheoremEnvironment::new(&[]);
            let context = pure_theorem_context(theorem, &predicates, &functions).unwrap();
            let Ensure::Proposition(surface_goal) = theorem.ensures()[0].ensure() else {
                unreachable!()
            };
            let goal = lower_pure_theorem_proposition(
                theorem.name(),
                surface_goal,
                &context.values,
                &context.array_refs,
                &context.memory,
                &predicates,
                &functions,
            )
            .unwrap();
            let root = Proof::for_pure_surface_goal(
                theorem.name(),
                &context.requires,
                goal.clone(),
                surface_goal.clone(),
                &context,
                &predicates,
                &functions,
                &theorems,
            );
            let certificate = ProofCertificate::from_proof_tactics(
                theorem.ensures()[0].proof().tactics().unwrap(),
            )
            .unwrap();
            let before = crate::persistent::persistent_node_allocations();
            let instantiated = root.apply_step(certificate.steps()[0].clone()).unwrap();
            allocations.push(crate::persistent::persistent_node_allocations() - before);
            assert!(!instantiated.is_complete());
            assert_eq!(instantiated.goal(), Some(&goal));
            assert!(root.certificate().steps().is_empty());
            assert!(!root.facts().contains(&goal));
            assert!(instantiated.facts().contains(&goal));
            let completed = instantiated.apply_step(ProofStep::Assumption).unwrap();
            completed.completed_proposition().unwrap();
        }
        for pair in allocations.windows(2) {
            assert!(
                pair[1] <= pair[0] + 128,
                "instantiation must allocate only a logarithmic fact delta: {allocations:?}"
            );
        }
    }

    #[test]
    fn pure_instantiate_smart_caller_expands_and_reverifies() {
        let fixture = include_str!("../../../mdtests/pure_theorem_instantiate.md");
        let source = fixture
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        crate::surface::verify_c0_sources(source, &[]).unwrap();
        let expanded = crate::surface::expand_c0_claim_source_by_label(
            source,
            &[],
            "instantiate_bound_caller.ensures_0",
        )
        .unwrap();
        assert_ne!(source, expanded);
        crate::surface::verify_c0_sources(&expanded, &[]).unwrap();
        let repeated = crate::surface::expand_c0_claim_source_by_label(
            &expanded,
            &[],
            "instantiate_bound_caller.ensures_0",
        )
        .unwrap();
        assert_eq!(expanded, repeated);
    }

    #[test]
    fn pure_instantiate_rejects_integer_binder_shadowing_an_int32_parameter() {
        let source = r#"
            theorem wrong_sort(x: int32) {
                requires forall (k: int32) { k == k };
                ensures forall (x: Integer) { x == x } by {
                    intro();
                    instantiate(forall (k: int32) { k == k }, x) using {}
                    normalize();
                }
            }
        "#;
        let error = verify_instantiation_theorem(source).unwrap_err();
        assert!(
            error.message().contains("Integer binding"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn pure_instantiate_branch_continuations_keep_checked_sibling_proofs() {
        let source = r#"
            theorem branched(x: int32) {
                requires forall (k: int32) { k == k };
                requires x == 0 or x != 0;
                ensures x == x by {
                    if x == 0 {
                        instantiate(forall (k: int32) { k == k }, x) using {}
                    } else {
                        instantiate(forall (k: int32) { k == k }, x) using {}
                    }
                    assumption();
                }
            }
        "#;
        let cases = source
            .replace("if x == 0", "cases (x == 0 or x != 0)")
            .replace("} else {", "} {");
        for source in [source, cases.as_str()] {
            let verified = verify_instantiation_theorem(source).unwrap();
            assert!(verified.kernel_authority.is_some());
            let arms = match &verified.proof.as_ref().unwrap().steps()[0] {
                ProofStep::If {
                    then_proof,
                    else_proof,
                    ..
                } => [then_proof, else_proof],
                ProofStep::Cases {
                    left_proof,
                    right_proof,
                    ..
                } => [left_proof, right_proof],
                _ => panic!("the checked certificate must retain both branches"),
            };
            for arm in arms {
                assert!(matches!(
                    arm.steps(),
                    [ProofStep::InstantiateUsing { .. }, ProofStep::Assumption]
                ));
            }
            let prefix = source.split_once(" by {").unwrap().0;
            let expanded = format!(
                "{prefix} {}\n}}",
                format_proof_certificate(verified.proof.as_ref().unwrap())
            );
            assert!(
                verify_instantiation_theorem(&expanded)
                    .unwrap()
                    .kernel_authority
                    .is_some()
            );
            let wrong_sibling = source.replacen(
                "instantiate(forall (k: int32) { k == k }, x) using {}",
                "",
                1,
            );
            let error = verify_instantiation_theorem(&wrong_sibling).unwrap_err();
            assert!(
                error.message().contains("assumption"),
                "{}",
                error.message()
            );
        }
    }

    fn verify_standard_declaration(source: &str) -> Result<(), ClickError> {
        let file = crate::surface::parser::parse_file_items(source)?;
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions())
            .with_contracts(file.contract_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());
        let theorem = file
            .theorem_definitions()
            .first()
            .ok_or_else(|| ClickError::new("test source did not contain a theorem"))?;
        let context =
            pure_theorem_context(theorem, &predicate_environment, &click_function_environment)?;
        let ensure = theorem
            .ensures()
            .first()
            .ok_or_else(|| ClickError::new("test source did not contain an ensures clause"))?;
        let Ensure::Proposition(surface_goal) = ensure.ensure() else {
            return Err(ClickError::new("test source did not contain a proposition"));
        };
        let (goal, _) = lower_pure_theorem_proposition_recording_introductions(
            theorem.name(),
            surface_goal,
            &assumptions_from_propositions(&context.requires),
            &context.values,
            &context.array_refs,
            &BTreeMap::new(),
            &context.integer_values,
            &context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .map_err(ClickError::new)?;
        verify_kernel_standard_theorem_axiom(theorem, 0, ensure, theorem.name(), &context, goal)
            .map(|_| ())
    }

    #[test]
    fn int32_order_to_integer_kernel_declaration_checks_its_guard_and_conclusion() {
        let source = r#"
theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}
"#;
        verify_standard_declaration(source)
            .expect("the checked order axiom declaration should verify");

        for invalid in [
            source.replace("requires left <= right;", ""),
            source.replace("requires left <= right;", "requires right <= left;"),
            source.replace(
                "ensures to_integer(left) <= to_integer(right);",
                "ensures to_integer(right) <= to_integer(left);",
            ),
        ] {
            assert!(
                verify_standard_declaration(&invalid).is_err(),
                "invalid order axiom declaration was accepted: {invalid}"
            );
        }
    }
}
