use super::diagnostics::*;
use super::validation::proof_step_name;
use super::*;

pub(super) fn verify_theorem_definitions(
    theorem_definitions: &[TheoremDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = TheoremEnvironment::new(&[]);
    for theorem in theorem_definitions {
        let context =
            pure_theorem_context(theorem, predicate_environment, click_function_environment)?;
        for (ensure_index, ensure_clause) in theorem.ensures().iter().enumerate() {
            let claim_label = theorem_claim_label(theorem.name(), ensure_index, ensure_clause);
            let theorem = verify_theorem_ensure(
                theorem,
                ensure_index,
                ensure_clause,
                &claim_label,
                &context,
                predicate_environment,
                click_function_environment,
                &theorem_environment,
            )?;
            verified.push(theorem);
        }
        theorem_environment.insert(theorem.clone());
    }
    Ok(verified)
}

#[derive(Clone, Debug)]
struct PureTheoremContext {
    memory: CMemory,
    values: BTreeMap<String, CValue>,
    array_refs: ClickArrayRefs,
    requires: Vec<Proposition>,
}

fn pure_theorem_context(
    theorem: &TheoremDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<PureTheoremContext, ClickError> {
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(theorem.parameters());
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
            lower_pure_theorem_proposition(
                theorem.name(),
                proposition,
                &values,
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
    Ok(PureTheoremContext {
        memory,
        values,
        array_refs,
        requires,
    })
}

pub(super) fn pure_theorem_parameter_values(
    parameters: &[FunctionParameter],
) -> BTreeMap<String, CValue> {
    parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let value = match parameter.c_type() {
                C0Type::Int32 => CValue::Int32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt8 => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int32Pointer | C0Type::Int32Array(_) => CValue::Pointer(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }),
                C0Type::UInt8Pointer | C0Type::UInt8Array(_) => CValue::Pointer(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                }),
            };
            (parameter.name().to_string(), value)
        })
        .collect()
}

pub(super) fn pure_theorem_array_refs(
    parameters: &[FunctionParameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.c_type())?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.clone(),
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
) -> Result<VerifiedPureTheorem, ClickError> {
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(format!(
            "pure theorem `{}` currently supports proposition `ensures` clauses only",
            theorem.name()
        )));
    };
    let goal = lower_pure_theorem_proposition(
        theorem.name(),
        surface_goal,
        &context.values,
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

    match ensure_clause.proof() {
        Proof::Tactic(Tactic::Auto) => {
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
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::Pure,
                proof_steps: None,
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
        Proof::Tactic(Tactic::Simp) => {
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
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::Simp,
                proof_steps: None,
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
        Proof::Tactic(Tactic::Frame) => Err(ClickError::new(format!(
            "`frame` cannot prove pure theorem `{claim_label}`"
        ))),
        Proof::Steps(steps) => {
            if steps.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` has an empty proof-step script"
                )));
            }
            let mut unfolded_predicates = Vec::new();
            let mut theorem_applications = Vec::new();
            let mut use_simp = false;
            for (step_index, step) in steps.iter().enumerate() {
                match step {
                    ProofStep::UnfoldPredicate(name) => {
                        if predicate_environment.get(name).is_none() {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` proof step {step_index}: unknown predicate `{name}`"
                            )));
                        }
                        if !unfolded_predicates.contains(name) {
                            unfolded_predicates.push(name.clone());
                        }
                    }
                    ProofStep::ApplyTheorem(application) => {
                        if theorem_environment.get(&application.name).is_none() {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` proof step {step_index}: unknown theorem `{}`",
                                application.name
                            )));
                        }
                        theorem_applications.push((step_index, application.clone()));
                    }
                    ProofStep::Simp => {
                        use_simp = true;
                    }
                    _ => {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` proof step {step_index}: `{}` cannot prove a pure theorem",
                            proof_step_name(step)
                        )));
                    }
                }
            }
            prove_pure_theorem_goal(
                claim_label,
                "proof steps",
                &context.requires,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                context,
                &theorem_applications,
                &unfolded_predicates,
                use_simp,
            )?;
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::ProofSteps,
                proof_steps: Some(steps.to_vec()),
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
    }
}

fn lower_pure_theorem_proposition(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let mut lowerer = KernelPropositionLowerer::new(
        values.clone(),
        array_refs.clone(),
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    lowerer
        .lower_requirement_proposition(proposition)
        .map_err(|error| {
            error
                .message()
                .replace("`requires`", &format!("pure theorem `{theorem_name}`"))
        })
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
    let application_context = TheoremApplicationContext {
        values: &context.values,
        array_refs: &context.array_refs,
        pre_state: &state,
        post_state: &state,
        result: None,
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
    let assumptions = assumptions_from_propositions(&available);
    if assumptions.proves(&goal) {
        return Ok(());
    }
    if use_simp {
        match simp_proposition(&goal, &assumptions) {
            SimpProposition::True => return Ok(()),
            simplified => {
                return Err(ClickError::new(format!(
                    "`{proof_name}` failed for `{claim_label}`: simplified proposition was not true: {simplified:?}\n  {}",
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

struct TheoremApplicationContext<'a> {
    values: &'a BTreeMap<String, CValue>,
    array_refs: &'a ClickArrayRefs,
    pre_state: &'a CState,
    post_state: &'a CState,
    result: Option<&'a CValue>,
}

fn apply_theorem_applications_to_available(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    mut available: Vec<Proposition>,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    for (step_index, application) in theorem_applications {
        available = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &available,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, *step_index, message)
        })?;
        let conclusions = instantiate_theorem_application(
            theorem_environment,
            application,
            claim_label,
            path_index,
            *step_index,
            &available,
            context,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )?;
        for conclusion in conclusions {
            if !available.contains(&conclusion) {
                available.push(conclusion);
            }
        }
    }
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &available,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, 0, message))
}

fn instantiate_theorem_application(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    step_index: usize,
    available: &[Proposition],
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        theorem_application_error(
            claim_label,
            path_index,
            step_index,
            format!("unknown theorem `{}`", application.name),
        )
    })?;
    if application.arguments.len() != theorem.parameters().len() {
        return Err(theorem_application_error(
            claim_label,
            path_index,
            step_index,
            format!(
                "theorem `{}` expects {} argument(s), got {}",
                theorem.name(),
                theorem.parameters().len(),
                application.arguments.len()
            ),
        ));
    }

    let assumptions = assumptions_from_propositions(available);
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        &assumptions,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, step_index, message))?;
    let mut lowerer = KernelPropositionLowerer::new(
        values,
        array_refs,
        context.post_state.memory().clone(),
        predicate_environment,
        click_function_environment,
    );

    for requirement in theorem.requires() {
        let Some(requirement) = requirement.proposition() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                step_index,
                format!(
                    "theorem `{}` has a non-proposition requirement that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let mut lowered = lowerer
            .lower_requirement_proposition(requirement)
            .map_err(|error| {
                theorem_application_error(
                    claim_label,
                    path_index,
                    step_index,
                    format!(
                        "could not lower theorem `{}` requirement: {}",
                        theorem.name(),
                        error.message()
                    ),
                )
            })?;
        lowered = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &lowered,
            &assumptions,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, step_index, message)
        })?;
        if !assumptions.proves(&lowered)
            && !matches!(
                simp_proposition(&lowered, &assumptions),
                SimpProposition::True
            )
        {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                step_index,
                format!(
                    "could not prove requirement for theorem `{}`: {}",
                    theorem.name(),
                    describe_missing_pure_fact(&lowered, available, &[], &[], &[], &[])
                ),
            ));
        }
    }

    let mut conclusions = Vec::new();
    for ensure in theorem.ensures() {
        let Ensure::Proposition(conclusion) = ensure.ensure() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                step_index,
                format!(
                    "theorem `{}` has a non-proposition conclusion that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let conclusion = lowerer
            .lower_requirement_proposition(conclusion)
            .map_err(|error| {
                theorem_application_error(
                    claim_label,
                    path_index,
                    step_index,
                    format!(
                        "could not lower theorem `{}` conclusion: {}",
                        theorem.name(),
                        error.message()
                    ),
                )
            })?;
        conclusions.push(conclusion);
    }
    Ok(conclusions)
}

fn theorem_application_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let mut active_functions = BTreeSet::new();
    let mut values = BTreeMap::new();
    let mut array_refs = BTreeMap::new();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                &mut active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "theorem `{}` parameter `{}` is not an array-ref parameter",
                        theorem.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    theorem.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            values.insert(
                parameter.name().to_string(),
                CValue::Pointer(array_ref.pointer.clone()),
            );
            array_refs.insert(parameter.name().to_string(), array_ref);
        } else {
            let value = evaluate_contract_expression_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                &mut active_functions,
            )?;
            if !c_value_matches_click_type(&value, parameter.c_type()) {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {}, got {value:?}",
                    theorem.name(),
                    parameter.name(),
                    describe_c0_type(parameter.c_type())
                ));
            }
            values.insert(parameter.name().to_string(), value);
        }
    }
    Ok((values, array_refs))
}

fn theorem_application_error(
    claim_label: &str,
    path_index: Option<usize>,
    step_index: usize,
    message: impl Into<String>,
) -> ClickError {
    let path = path_index
        .map(|index| format!(" path {index},"))
        .unwrap_or_default();
    ClickError::new(format!(
        "`{claim_label}`{path} proof step {step_index}: `apply` failed: {}",
        message.into()
    ))
}

#[derive(Clone, Copy)]
pub(super) enum FunctionClaimRef<'a> {
    Effect(usize, &'a EffectClause),
    Ensure(usize, &'a EnsureClause),
}

impl<'a> FunctionClaimRef<'a> {
    pub(super) fn proof(self) -> &'a Proof {
        match self {
            Self::Effect(_, clause) => clause.proof(),
            Self::Ensure(_, clause) => clause.proof(),
        }
    }

    fn verified_claim(self) -> VerifiedClaim {
        match self {
            Self::Effect(index, clause) => VerifiedClaim::Effect {
                index,
                clause: clause.clone(),
            },
            Self::Ensure(index, clause) => VerifiedClaim::Ensure {
                index,
                clause: clause.clone(),
            },
        }
    }
}

pub(super) fn function_claims(function_block: &FunctionBlock) -> Vec<FunctionClaimRef<'_>> {
    function_block
        .effects()
        .iter()
        .enumerate()
        .map(|(index, clause)| FunctionClaimRef::Effect(index, clause))
        .chain(
            function_block
                .ensures()
                .iter()
                .enumerate()
                .map(|(index, clause)| FunctionClaimRef::Ensure(index, clause)),
        )
        .collect()
}

pub(super) fn prove_claim_by_auto(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let (mut state, arguments, requirement_pure_facts) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    let requirement_pure_facts = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_pure_facts,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        claim_label,
    )?;
    state = project_initial_view_composite_resources(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &requirement_pure_facts,
        claim_label,
    )?;
    let requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        &state,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let vc_execution = prove_symbolic_c_function_verification_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions.clone(),
        function_environment.clone(),
    );
    if let Some(error) = execution_obligation_error(
        &vc_execution,
        claim_label,
        &requirement_pure_facts,
        state.resources().facts(),
        parsed_function.parameters(),
        &arguments,
    ) {
        return Err(error);
    }
    let loop_verification_error = match prove_claim_from_execution(
        &vc_execution,
        AutoExecutionKind::LoopVerification,
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        resource_environment,
    ) {
        Ok(theorems) => {
            let proof_steps = certified_proof_steps(
                source_path,
                function_block,
                parsed_function,
                claim,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                auto_loop_verification_proof_step_candidates(function_block, claim),
            );
            return Ok(with_proof_steps(theorems, proof_steps));
        }
        Err(error) => Some(error),
    };
    let execution = prove_symbolic_c_function_execution_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
    );
    if let Some(error) = execution_obligation_error(
        &execution,
        claim_label,
        &requirement_pure_facts,
        state.resources().facts(),
        parsed_function.parameters(),
        &arguments,
    ) {
        if let Some(loop_verification_error) = loop_verification_error {
            return Err(loop_verification_error);
        }
        return Err(error);
    }
    let theorems = prove_claim_from_execution(
        &execution,
        AutoExecutionKind::BoundedExecution {
            environment: function_environment,
        },
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let proof_steps = certified_proof_steps(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        bounded_execution_proof_step_candidates(claim),
    );
    Ok(with_proof_steps(theorems, proof_steps))
}

pub(super) fn prove_claim_by_frame(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
        return Err(ClickError::new(format!(
            "`frame` only proves effect clauses for `{claim_label}`; use `by auto;` or `by simp;` for postconditions"
        )));
    }

    let (mut state, arguments, requirement_pure_facts) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    let requirement_pure_facts = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_pure_facts,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        claim_label,
    )?;
    state = project_initial_view_composite_resources(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &requirement_pure_facts,
        claim_label,
    )?;
    let requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        &state,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let execution = prove_symbolic_c_function_verification_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
    );
    if let Some(error) = execution_obligation_error_for_tactic(
        "frame",
        &execution,
        claim_label,
        &requirement_pure_facts,
        state.resources().facts(),
        parsed_function.parameters(),
        &arguments,
    ) {
        return Err(error);
    }

    let theorems = prove_claim_from_execution(
        &execution,
        AutoExecutionKind::Frame,
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let proof_steps = certified_proof_steps(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        frame_proof_step_candidates(),
    );
    Ok(with_proof_steps(theorems, proof_steps))
}

pub(super) fn prove_claim_by_simp(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if count_loops(parsed_function.body()) != 0 {
        return Err(ClickError::new(format!(
            "`simp` does not prove loop-backed claims for `{claim_label}`; use `by auto;`"
        )));
    }

    let (mut state, arguments, requirement_pure_facts) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    let requirement_pure_facts = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_pure_facts,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        claim_label,
    )?;
    state = project_initial_view_composite_resources(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &requirement_pure_facts,
        claim_label,
    )?;
    let requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        &state,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let proof_steps = certified_proof_steps(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        vec![vec![ProofStep::SymbolicExecute, ProofStep::Simp]],
    );
    let assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let execution = prove_symbolic_c_function_execution_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
    );
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`simp` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`simp` could not establish a direct execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`simp` failed for `{claim_label}` path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    &requirement_pure_facts,
                    state.resources().facts(),
                    parsed_function.parameters(),
                    &arguments,
                    path.facts()
                )
            )));
        }

        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`simp` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  pure facts: {}\n  execution pure facts: {}",
                    describe_pure_facts(&requirement_pure_facts),
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        path_requirements = project_outcome_resource_facts(
            resource_environment,
            parsed_function.parameters(),
            &arguments,
            &state,
            &outcome,
            &path_requirements,
            predicate_environment,
            click_function_environment,
            claim_label,
            path_index,
        )?;
        check_function_claim_by_simp(
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            claim,
            parsed_function.parameters(),
            &arguments,
            &state,
            &outcome,
            predicate_environment,
            click_function_environment,
            &[],
        )?;
        let specification = c_function_specification(
            state.clone(),
            arguments.clone(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = prove_c_function_satisfies_specification_with_environment(
            function.clone(),
            specification.clone(),
            Assumptions::new(),
            function_environment.clone(),
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`simp` failed for `{claim_label}` path {path_index}: execution did not satisfy the packaged specification\n  execution pure facts: {}",
                describe_execution_pure_facts(path.facts())
            ))
        })?;

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind: ProofKind::Simp,
            proof_steps: proof_steps.clone(),
            specification,
            theorem,
        });
    }

    Ok(verified)
}

#[derive(Default)]
struct ProofStepReplayState {
    execution_point: ProofExecutionPoint,
    execution_start_state: Option<CState>,
    loop_vcs: BTreeSet<usize>,
    frames: BTreeSet<Option<CodeRegionRef>>,
    unfolded_predicates: Vec<String>,
    theorem_applications: Vec<(usize, TheoremApplication)>,
    resource_folds: Vec<ResourceClause>,
    simp: bool,
}

#[derive(Default)]
enum ProofExecutionPoint {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: CStatement,
    },
    FunctionExit {
        execution: crate::kernel::SymbolicCExecution,
        mode: ProofStepExecutionMode,
    },
}

impl ProofStepReplayState {
    fn is_at_function_exit(&self) -> bool {
        matches!(
            self.execution_point,
            ProofExecutionPoint::FunctionExit { .. }
        )
    }

    fn is_at_function_entry(&self) -> bool {
        matches!(self.execution_point, ProofExecutionPoint::FunctionEntry)
    }

    fn execution(&self) -> Option<&crate::kernel::SymbolicCExecution> {
        match &self.execution_point {
            ProofExecutionPoint::FunctionEntry | ProofExecutionPoint::StatementEntry { .. } => None,
            ProofExecutionPoint::FunctionExit { execution, .. } => Some(execution),
        }
    }

    fn execution_mode(&self) -> Option<ProofStepExecutionMode> {
        match self.execution_point {
            ProofExecutionPoint::FunctionEntry | ProofExecutionPoint::StatementEntry { .. } => None,
            ProofExecutionPoint::FunctionExit { mode, .. } => Some(mode),
        }
    }

    fn execution_start_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        self.execution_start_state.as_ref().unwrap_or(current_state)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProofStepExecutionMode {
    Verification,
    Bounded,
}

pub(super) fn prove_claim_by_steps(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    steps: &[ProofStep],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if steps.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty proof-step script"
        )));
    }

    let (mut state, arguments, mut requirement_pure_facts) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    requirement_pure_facts = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_pure_facts,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    state = materialize_folded_composite_resource_cells(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        claim_label,
    )?;
    state = project_initial_view_composite_resources(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        state,
        &requirement_pure_facts,
        claim_label,
    )?;
    requirement_pure_facts = project_initial_resource_facts(
        resource_environment,
        parsed_function.parameters(),
        &arguments,
        &state,
        &requirement_pure_facts,
        predicate_environment,
        click_function_environment,
        claim_label,
    )?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let mut assumptions = assumptions_from_propositions(&requirement_pure_facts);
    let mut replay = ProofStepReplayState::default();

    for (step_index, step) in steps.iter().enumerate() {
        match step {
            ProofStep::UnfoldResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `unfold` must run before execution reaches function exit"
                    )));
                }
                state = unfold_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    &arguments,
                    state,
                    &mut requirement_pure_facts,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    step_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofStep::ObserveResource(resource) => {
                if replay.is_at_function_exit() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `observe` must run before execution reaches function exit"
                    )));
                }
                state = observe_composite_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    &arguments,
                    state,
                    &mut requirement_pure_facts,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    step_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofStep::ExecuteStep => {
                execute_step_from_execution_point(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    &function,
                    parsed_function.parameters(),
                    &arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    step_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofStep::SymbolicExecute | ProofStep::ExecuteRest => {
                execute_rest_from_execution_point(
                    &mut replay,
                    &mut state,
                    &requirement_pure_facts,
                    &function,
                    &arguments,
                    &assumptions,
                    function_environment,
                    claim_label,
                    step_index,
                    proof_step_name(step),
                )?;
            }
            ProofStep::ExecuteUntil(region_ref) => {
                let code_region =
                    resolve_code_region_ref(function_block, region_ref, claim_label, step_index)?;
                let CodeRegion::Statement(statement_index) = code_region else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `execute_until` expects a statement region"
                    )));
                };
                execute_until_statement(
                    &mut replay,
                    &mut state,
                    &mut requirement_pure_facts,
                    &function,
                    parsed_function.parameters(),
                    &arguments,
                    &assumptions,
                    function_environment,
                    statement_index,
                    claim_label,
                    step_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_pure_facts);
            }
            ProofStep::BoundedExecute => {
                if !replay.is_at_function_entry() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `bounded_execute` is only supported from function entry"
                    )));
                }
                set_replay_execution(
                    &mut replay,
                    ProofStepExecutionMode::Bounded,
                    claim_label,
                    step_index,
                    "bounded_execute",
                    state.clone(),
                    prove_symbolic_c_function_execution_paths_with_environment(
                        state.clone(),
                        function.clone(),
                        arguments.clone(),
                        assumptions.clone(),
                        function_environment.clone(),
                    ),
                )?;
            }
            ProofStep::LoopVc(region_ref) => {
                require_step_execution(&replay, claim_label, step_index, "loop_vc")?;
                require_verification_execution(&replay, claim_label, step_index, "loop_vc")?;
                let code_region =
                    resolve_code_region_ref(function_block, region_ref, claim_label, step_index)?;
                let CodeRegion::Loop(loop_index) = code_region else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `loop_vc` expects a loop code region"
                    )));
                };
                validate_loop_code_region(parsed_function, loop_index, claim_label, step_index)?;
                validate_loop_vc_step(
                    replay.execution().expect("execution should exist"),
                    loop_index,
                    claim_label,
                    step_index,
                )?;
                replay.loop_vcs.insert(loop_index);
            }
            ProofStep::Frame(region_ref) => {
                require_step_execution(&replay, claim_label, step_index, "frame")?;
                let code_region = region_ref
                    .as_ref()
                    .map(|region_ref| {
                        resolve_code_region_ref(function_block, region_ref, claim_label, step_index)
                    })
                    .transpose()?;
                validate_frame_code_region(
                    function_block,
                    parsed_function,
                    code_region,
                    claim,
                    claim_label,
                    step_index,
                )?;
                match code_region {
                    None | Some(CodeRegion::Function) => {
                        validate_function_frame_step(
                            replay.execution().expect("execution should exist"),
                            claim,
                            claim_label,
                            step_index,
                            parsed_function.parameters(),
                            &arguments,
                            &state,
                            &requirement_pure_facts,
                        )?;
                    }
                    Some(CodeRegion::Loop(_)) => {
                        require_verification_execution(&replay, claim_label, step_index, "frame")?;
                    }
                    Some(CodeRegion::Statement(_)) => {}
                }
                replay.frames.insert(region_ref.clone());
            }
            ProofStep::UnfoldPredicate(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: unknown predicate `{name}`"
                    )));
                }
                if !replay.unfolded_predicates.contains(name) {
                    replay.unfolded_predicates.push(name.clone());
                }
            }
            ProofStep::ApplyTheorem(application) => {
                require_step_execution(&replay, claim_label, step_index, "apply")?;
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                replay
                    .theorem_applications
                    .push((step_index, application.clone()));
            }
            ProofStep::FoldResource(resource) => {
                require_step_execution(&replay, claim_label, step_index, "fold")?;
                replay.resource_folds.push(resource.clone());
            }
            ProofStep::Witness(_) => {
                require_step_execution(&replay, claim_label, step_index, "witness")?;
            }
            ProofStep::Choose(_) => {
                require_step_execution(&replay, claim_label, step_index, "choose")?;
            }
            ProofStep::Simp => {
                require_step_execution(&replay, claim_label, step_index, "simp")?;
                replay.simp = true;
            }
        }
    }

    let execution = replay.execution().ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` proof-step script must reach function exit with `execute_step()`, `execute_rest()`, `symbolic_execute()`, or `bounded_execute()`"
        ))
    })?;
    prove_claim_from_steps_execution(
        execution,
        replay
            .execution_mode()
            .expect("proof-step execution should have an execution mode"),
        source_path,
        function_block,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        parsed_function.parameters(),
        &function,
        replay.execution_start_state(&state),
        &arguments,
        &requirement_pure_facts,
        &replay.unfolded_predicates,
        &replay.theorem_applications,
        &replay.resource_folds,
        replay.simp,
        steps,
    )
}

#[allow(clippy::too_many_arguments)]
fn execute_step_from_execution_point(
    replay: &mut ProofStepReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    assumptions: &Assumptions,
    function_environment: &CFunctionEnvironment,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    let execution_point = &replay.execution_point;
    let (execution_start_state, current_state, step_statement, remaining) = match execution_point {
        ProofExecutionPoint::FunctionEntry => {
            let execution_start_state = state.clone();
            let current_state = c_function_entry_state(&execution_start_state, function, arguments)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `execute_step` could not bind function arguments"
                    ))
                })?;
            let (step_statement, remaining) = match split_next_straight_line_statement(
                function.body(),
            ) {
                Ok(split) => split,
                Err(message) => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `execute_step` failed: {message}"
                    )));
                }
            };
            (
                execution_start_state,
                current_state,
                step_statement,
                remaining,
            )
        }
        ProofExecutionPoint::StatementEntry { remaining } => {
            let execution_start_state = replay.execution_start_state.clone().ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `execute_step` has no execution start state"
                ))
            })?;
            let (step_statement, remaining) = match split_next_straight_line_statement(remaining) {
                Ok(split) => split,
                Err(message) => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `execute_step` failed: {message}"
                    )));
                }
            };
            (
                execution_start_state,
                state.clone(),
                step_statement,
                remaining,
            )
        }
        ProofExecutionPoint::FunctionExit { .. } => {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `execute_step` cannot run after execution already reached function exit"
            )));
        }
    };

    let current_resources = current_state.resources().facts().to_vec();
    let execution = prove_symbolic_c_execution_paths_with_environment(
        current_state,
        step_statement,
        assumptions.clone(),
        function_environment.clone(),
    );
    let path = single_statement_step_path(
        &execution,
        claim_label,
        step_index,
        "execute_step",
        available_pure_facts,
        &current_resources,
        parameters,
        arguments,
    )?;
    let execution_pure_facts = path.facts().to_vec();
    let outcome = match implication_body(path.theorem().proposition()) {
        Proposition::CStatementExecutes { outcome, .. } => outcome.clone(),
        proposition => {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `execute_step` saw unexpected step theorem {proposition:?}"
            )));
        }
    };

    match outcome {
        CStatementOutcome::Normal(next_state) => {
            let Some(remaining) = remaining else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `execute_step` reached the end of the function without a return"
                )));
            };
            available_pure_facts.extend(
                execution_pure_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            replay.execution_start_state = Some(execution_start_state);
            replay.execution_point = ProofExecutionPoint::StatementEntry { remaining };
            *state = next_state;
        }
        CStatementOutcome::Return { .. } => {
            let mut path_pure_facts = available_pure_facts.clone();
            path_pure_facts.extend(
                execution_pure_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            let return_assumptions = assumptions_from_propositions(&path_pure_facts);
            let (outcome, obligations) = c_function_outcome_from_statement_outcome(
                &execution_start_state,
                function,
                outcome,
                path.obligations().to_vec(),
                &return_assumptions,
            );
            let completed = certify_c_function_execution_paths_from_outcomes(
                execution_start_state.clone(),
                function.clone(),
                arguments.to_vec(),
                assumptions.clone(),
                vec![(outcome, execution_pure_facts, obligations)],
            );
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                ProofStepExecutionMode::Verification,
                claim_label,
                step_index,
                "execute_step",
                execution_start_state,
                completed,
            )?;
            *state = replay_state;
        }
        CStatementOutcome::UndefinedBehavior(kind) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `execute_step` produced undefined behavior: {kind:?}\n{}",
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
        CStatementOutcome::RuntimeError(error) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `execute_step` produced runtime error: {error:?}\n{}",
                describe_proof_context(
                    available_pure_facts,
                    &current_resources,
                    parameters,
                    arguments,
                    &execution_pure_facts
                )
            )));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_rest_from_execution_point(
    replay: &mut ProofStepReplayState,
    state: &mut CState,
    available_pure_facts: &[Proposition],
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
    function_environment: &CFunctionEnvironment,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
) -> Result<(), ClickError> {
    match &replay.execution_point {
        ProofExecutionPoint::FunctionEntry => {
            set_replay_execution(
                replay,
                ProofStepExecutionMode::Verification,
                claim_label,
                step_index,
                step_name,
                state.clone(),
                prove_symbolic_c_function_verification_paths_with_environment(
                    state.clone(),
                    function.clone(),
                    arguments.to_vec(),
                    assumptions.clone(),
                    function_environment.clone(),
                ),
            )?;
        }
        ProofExecutionPoint::StatementEntry { remaining, .. } => {
            let execution = prove_symbolic_c_execution_paths_with_environment(
                state.clone(),
                remaining.clone(),
                assumptions.clone(),
                function_environment.clone(),
            );
            let Some(execution_start_state) = replay.execution_start_state.clone() else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `{step_name}` has no execution start state"
                )));
            };
            let completed = complete_segmented_function_execution(
                execution,
                &execution_start_state,
                function,
                arguments,
                available_pure_facts,
                assumptions,
                claim_label,
                step_index,
                step_name,
            )?;
            let replay_state = execution_start_state.clone();
            set_replay_execution(
                replay,
                ProofStepExecutionMode::Verification,
                claim_label,
                step_index,
                step_name,
                execution_start_state,
                completed,
            )?;
            *state = replay_state;
        }
        ProofExecutionPoint::FunctionExit { .. } => {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `{step_name}` cannot run after execution already reached function exit"
            )));
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn execute_until_statement(
    replay: &mut ProofStepReplayState,
    state: &mut CState,
    available_pure_facts: &mut Vec<Proposition>,
    function: &CFunction,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    assumptions: &Assumptions,
    function_environment: &CFunctionEnvironment,
    statement_index: usize,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    if !replay.is_at_function_entry() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `execute_until` is currently supported only from function entry"
        )));
    }
    let (prefix, remaining) =
        split_straight_line_statement_prefix(function.body(), statement_index).map_err(
            |message| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `execute_until(statement({statement_index}))` failed: {message}"
                ))
            },
        )?;
    let execution_start_state = state.clone();
    let mut callee_state = c_function_entry_state(&execution_start_state, function, arguments)
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `execute_until` could not bind function arguments"
            ))
        })?;

    if let Some(prefix) = prefix {
        let current_resources = callee_state.resources().facts().to_vec();
        let execution = prove_symbolic_c_execution_paths_with_environment(
            callee_state,
            prefix,
            assumptions.clone(),
            function_environment.clone(),
        );
        let prefix_path = single_normal_statement_path(
            &execution,
            claim_label,
            step_index,
            "execute_until",
            available_pure_facts,
            &current_resources,
            parameters,
            arguments,
        )?;
        available_pure_facts.extend(
            prefix_path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        let Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Normal(next_state),
            ..
        } = implication_body(prefix_path.theorem().proposition())
        else {
            unreachable!("single_normal_statement_path should return a normal statement path");
        };
        callee_state = next_state.clone();
    }

    replay.execution_start_state = Some(execution_start_state);
    replay.execution_point = ProofExecutionPoint::StatementEntry { remaining };
    *state = callee_state;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn complete_segmented_function_execution(
    execution: crate::kernel::SymbolicCExecution,
    execution_start_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    available_pure_facts: &[Proposition],
    assumptions: &Assumptions,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
) -> Result<crate::kernel::SymbolicCExecution, ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` hit execution limit {limit:?}"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` produced no suffix execution paths"
        )));
    }
    let mut completed_paths = Vec::new();
    for path in execution.paths() {
        let Proposition::CStatementExecutes { outcome, .. } =
            implication_body(path.theorem().proposition())
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `{step_name}` saw unexpected suffix theorem"
            )));
        };
        let mut path_pure_facts = available_pure_facts.to_vec();
        path_pure_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        let return_assumptions = assumptions_from_propositions(&path_pure_facts);
        let (outcome, obligations) = c_function_outcome_from_statement_outcome(
            execution_start_state,
            function,
            outcome.clone(),
            path.obligations().to_vec(),
            &return_assumptions,
        );
        completed_paths.push((outcome, path.facts().to_vec(), obligations));
    }
    Ok(certify_c_function_execution_paths_from_outcomes(
        execution_start_state.clone(),
        function.clone(),
        arguments.to_vec(),
        assumptions.clone(),
        completed_paths,
    ))
}

fn single_statement_step_path<'a>(
    execution: &'a crate::kernel::SymbolicCExecution,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
    available_pure_facts: &[Proposition],
    resources: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<&'a crate::kernel::SymbolicCExecutionPath, ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` hit execution limit {limit:?}"
        )));
    }
    if execution.paths().len() != 1 {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` currently requires exactly one statement path, got {}",
            execution.paths().len()
        )));
    }
    let path = &execution.paths()[0];
    if !path.obligations().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` failed: {}",
            describe_missing_proof_obligations(
                path.obligations(),
                available_pure_facts,
                resources,
                parameters,
                arguments,
                path.facts()
            )
        )));
    }
    Ok(path)
}

fn single_normal_statement_path<'a>(
    execution: &'a crate::kernel::SymbolicCExecution,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
    available_pure_facts: &[Proposition],
    resources: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<&'a crate::kernel::SymbolicCExecutionPath, ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` hit execution limit {limit:?}"
        )));
    }
    if execution.paths().len() != 1 {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` currently requires exactly one straight-line prefix path, got {}",
            execution.paths().len()
        )));
    }
    let path = &execution.paths()[0];
    if !path.obligations().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` failed: {}",
            describe_missing_proof_obligations(
                path.obligations(),
                available_pure_facts,
                resources,
                parameters,
                arguments,
                path.facts()
            )
        )));
    }
    match implication_body(path.theorem().proposition()) {
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Normal(_),
            ..
        } => Ok(path),
        Proposition::CStatementExecutes { outcome, .. } => Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` prefix did not stop at a normal execution point: {outcome:?}"
        ))),
        proposition => Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` saw unexpected prefix theorem {proposition:?}"
        ))),
    }
}

fn split_next_straight_line_statement(
    statement: &CStatement,
) -> Result<(CStatement, Option<CStatement>), String> {
    let mut statements = Vec::new();
    flatten_top_level_sequence(statement, &mut statements)?;
    let (first, rest) = statements
        .split_first()
        .expect("a CStatement should flatten to at least one statement");
    if !is_straight_line_statement(first) {
        return Err("next statement is not a supported straight-line statement".to_string());
    }
    Ok((first.clone(), sequence_from_statements(rest)))
}

fn split_straight_line_statement_prefix(
    statement: &CStatement,
    statement_index: usize,
) -> Result<(Option<CStatement>, CStatement), String> {
    let mut statements = Vec::new();
    flatten_top_level_sequence(statement, &mut statements)?;
    if statement_index >= statements.len() {
        return Err(format!(
            "function has no `statement({statement_index})`; it contains {} statement(s)",
            statements.len()
        ));
    }
    for (index, statement) in statements.iter().take(statement_index).enumerate() {
        if !is_straight_line_statement(statement) {
            return Err(format!(
                "prefix statement({index}) is not a supported straight-line statement"
            ));
        }
    }
    let prefix = sequence_from_statements(&statements[..statement_index]);
    let remaining = sequence_from_statements(&statements[statement_index..])
        .expect("statement_index bounds check should leave a non-empty suffix");
    Ok((prefix, remaining))
}

fn flatten_top_level_sequence(
    statement: &CStatement,
    statements: &mut Vec<CStatement>,
) -> Result<(), String> {
    match statement {
        CStatement::Seq(first, second) => {
            flatten_top_level_sequence(first, statements)?;
            flatten_top_level_sequence(second, statements)
        }
        statement => {
            statements.push(statement.clone());
            Ok(())
        }
    }
}

fn sequence_from_statements(statements: &[CStatement]) -> Option<CStatement> {
    let (first, rest) = statements.split_first()?;
    Some(
        rest.iter()
            .cloned()
            .fold(first.clone(), |acc, statement| c_seq(acc, statement)),
    )
}

fn is_straight_line_statement(statement: &CStatement) -> bool {
    !matches!(statement, CStatement::If { .. } | CStatement::While { .. })
}

fn set_replay_execution(
    replay: &mut ProofStepReplayState,
    mode: ProofStepExecutionMode,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
    execution_start_state: CState,
    execution: crate::kernel::SymbolicCExecution,
) -> Result<(), ClickError> {
    if let Some(existing) = replay.execution_mode() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` cannot run after {existing:?} execution already reached function exit"
        )));
    }
    replay.execution_start_state = Some(execution_start_state);
    replay.execution_point = ProofExecutionPoint::FunctionExit { execution, mode };
    Ok(())
}

fn require_step_execution(
    replay: &ProofStepReplayState,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
) -> Result<(), ClickError> {
    if !replay.is_at_function_exit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` requires execution to reach function exit first"
        )));
    }
    Ok(())
}

fn require_verification_execution(
    replay: &ProofStepReplayState,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
) -> Result<(), ClickError> {
    if replay.execution_mode() != Some(ProofStepExecutionMode::Verification) {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` requires verification execution rather than bounded execution"
        )));
    }
    Ok(())
}

fn materialize_folded_composite_resource_cells(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    claim_label: &str,
) -> Result<CState, ClickError> {
    let memory = materialize_folded_composite_resource_memory(
        resource_environment,
        parameters,
        arguments,
        &state,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    Ok(state.with_memory(memory))
}

fn materialize_folded_composite_resource_memory(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Result<CMemory, String> {
    let mut memory = state.memory().clone();
    for resource in state.resources().facts() {
        let (name, resource_arguments) = match resource.resource() {
            CResource::Composite { name, arguments } => (name, arguments),
            CResource::Memory(_) | CResource::Token { .. } => {
                continue;
            }
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_value_substitutions(definition, resource_arguments).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        memory = materialize_composite_resource_memory(
            name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            memory,
        )?;
    }
    Ok(memory)
}

fn project_initial_view_composite_resources(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &[Proposition],
    claim_label: &str,
) -> Result<CState, ClickError> {
    let assumptions = assumptions_from_propositions(available_pure_facts);
    for resource in state.resources().facts().to_vec() {
        let CResourceFact::View(CResource::Composite {
            name,
            arguments: resource_arguments,
        }) = resource
        else {
            continue;
        };
        let Some(definition) = resource_environment.get(&name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        let substitutions =
            resource_value_substitutions(definition, &resource_arguments).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` setup failed: could not project view resource `{name}`: {message}"
                ))
            })?;
        let (memory, contained_resources) = instantiate_composite_resource_body_resources(
            &name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            state.memory().clone(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not project view resource `{name}`: {message}"
            ))
        })?;
        let viewed_contained_resources = contained_resources
            .facts()
            .iter()
            .filter_map(CResourceFact::core)
            .collect::<Vec<_>>();
        let resources = state
            .resources()
            .clone()
            .try_compose_with_facts(viewed_contained_resources, &assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` setup failed: observing view resource `{name}` produced {}",
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        state = state.with_memory(memory).with_resource_context(resources);
    }
    Ok(state)
}

fn project_initial_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let result = CValue::Int32(Bitvector32Term::Constant(0));
    let projected_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        &format!("`{claim_label}` setup"),
    )?;
    project_folded_resource_observable_facts(
        resource_environment,
        parameters,
        arguments,
        state,
        state,
        &result,
        &projected_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))
}

fn project_outcome_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    path_index: usize,
) -> Result<Vec<Proposition>, ClickError> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Ok(available_pure_facts.to_vec());
    };
    let projected_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        &format!("`{claim_label}` path {path_index}"),
    )?;
    project_folded_resource_observable_facts(
        resource_environment,
        parameters,
        arguments,
        pre_state,
        state,
        value,
        &projected_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}: could not project folded resource facts: {message}"
        ))
    })
}

fn project_resource_context_observable_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    resources: &ResourceContext,
    available_pure_facts: &[Proposition],
    context: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let mut propositions = available_pure_facts.to_vec();
    let facts = resources.observable_facts(&assumptions).map_err(|error| {
        ClickError::new(format!(
            "{context}: {}",
            describe_resource_context_validity_error(error, parameters, arguments)
        ))
    })?;
    for proposition in facts {
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
    Ok(propositions)
}

fn append_state_resource_context_observable_facts(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &mut Vec<Proposition>,
    context: &str,
) -> Result<(), ClickError> {
    *available_pure_facts = project_resource_context_observable_facts(
        parameters,
        arguments,
        state.resources(),
        available_pure_facts,
        context,
    )?;
    Ok(())
}

fn project_folded_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, String> {
    let mut propositions = available_pure_facts.to_vec();
    for resource in state.resources().facts() {
        project_held_resource_observable_facts(
            resource_environment,
            resource,
            parameters,
            arguments,
            pre_state,
            state.memory().clone(),
            result,
            &mut propositions,
            predicate_environment,
            click_function_environment,
        )?;
    }
    Ok(propositions)
}

fn observe_composite_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    step_index: usize,
) -> Result<CState, ClickError> {
    let definition = composite_resource_definition(
        resource_environment,
        resource,
        "observe",
        claim_label,
        step_index,
    )?;
    let abstract_resource = lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    if !state
        .resources()
        .satisfies_fact(&abstract_resource, &assumptions)
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `observe({})` failed: {}",
            describe_resource_clause(resource),
            describe_missing_resource_fact(
                &abstract_resource,
                available_pure_facts,
                state.resources().facts(),
                parameters,
                arguments,
                &[]
            )
        )));
    }
    let CResource::Composite {
        arguments: resource_arguments,
        ..
    } = abstract_resource.resource()
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `observe` expects a composite resource"
        )));
    };
    let (memory, contained_resources) = project_composite_resource_observable_facts(
        resource_environment,
        definition,
        &resource_arguments,
        parameters,
        arguments,
        &state,
        state.memory().clone(),
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: could not observe `{}`: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let viewed_contained_resources = contained_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::core)
        .collect::<Vec<_>>();
    let resources = state
        .resources()
        .clone()
        .try_compose_with_facts(viewed_contained_resources, &assumptions)
        .map_err(|error| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `observe({})` produced {}",
                describe_resource_clause(resource),
                describe_resource_context_validity_error(error, parameters, arguments)
            ))
        })?;
    Ok(state.with_memory(memory).with_resource_context(resources))
}

fn project_held_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    memory: CMemory,
    result: &CValue,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CMemory, String> {
    let (name, resource_arguments) = match resource.resource() {
        CResource::Composite { name, arguments } => (name, arguments),
        CResource::Memory(_) | CResource::Token { .. } => {
            return Ok(memory);
        }
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(memory);
    };
    project_composite_resource_observable_facts(
        resource_environment,
        definition,
        resource_arguments,
        parameters,
        arguments,
        pre_state,
        memory,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )
    .map(|(memory, _)| memory)
}

fn project_composite_resource_observable_facts(
    _resource_environment: &ResourceEnvironment,
    definition: &ResourceDefinition,
    resource_arguments: &[CValue],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    memory: CMemory,
    result: &CValue,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(CMemory, ResourceContext), String> {
    let Some(composite_body) = definition.composite_body() else {
        return Ok((memory, ResourceContext::new()));
    };

    let substitutions =
        resource_value_substitutions(definition, resource_arguments).map_err(|message| {
            format!(
                "could not instantiate resource `{}` facts: {message}",
                definition.name()
            )
        })?;
    let (memory, contained_resources) = instantiate_composite_resource_body_resources(
        definition.name(),
        composite_body,
        &substitutions,
        parameters,
        arguments,
        memory,
    )?;
    let fact_state = pre_state.clone().with_memory(memory.clone());

    append_composite_resource_observable_facts(
        definition,
        composite_body,
        &substitutions,
        &contained_resources,
        parameters,
        arguments,
        pre_state,
        &fact_state,
        result,
        available_pure_facts,
        predicate_environment,
        click_function_environment,
    )?;
    Ok((memory, contained_resources))
}

fn append_composite_resource_observable_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
    propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    append_resource_context_observable_facts(
        definition.name(),
        contained_resources,
        parameters,
        arguments,
        propositions,
    )?;

    append_composite_resource_declared_facts(
        definition,
        composite_body,
        substitutions,
        contained_resources,
        parameters,
        arguments,
        pre_state,
        fact_state,
        result,
        propositions,
        predicate_environment,
        click_function_environment,
    )
}

fn append_composite_resource_declared_facts(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
    propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), String> {
    for fact in composite_body.facts() {
        let fact = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        let lowered = lower_outcome_proposition(
            parameters,
            arguments,
            pre_state,
            fact_state,
            result,
            propositions,
            &fact,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            format!(
                "could not lower resource `{}` pure fact `{}`: {message}\n  pure facts: {}\n  resource facts: {}",
                definition.name(),
                describe_click_proposition(&fact),
                describe_pure_facts(propositions),
                describe_resource_facts(contained_resources.facts(), parameters, arguments)
            )
        })?;
        if !propositions.contains(&lowered) {
            propositions.push(lowered);
        }
    }
    Ok(())
}

fn append_resource_context_observable_facts(
    name: &str,
    resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    propositions: &mut Vec<Proposition>,
) -> Result<(), String> {
    let assumptions = assumptions_from_propositions(propositions);
    let facts = resources.observable_facts(&assumptions).map_err(|error| {
        format!(
            "composite resource `{name}` body has {}",
            describe_resource_context_validity_error(error, parameters, arguments)
        )
    })?;
    for proposition in facts {
        if !propositions.contains(&proposition) {
            propositions.push(proposition);
        }
    }
    Ok(())
}

fn describe_resource_context_validity_error(
    error: ResourceContextValidityError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            format!(
                "duplicate resource fact `{}`",
                describe_resource_fact(&resource, parameters, arguments)
            )
        }
        ResourceContextValidityError::OverlappingWriteResources { left, right } => {
            format!(
                "overlapping write resource facts `write({})` and `write({})`",
                describe_memory_range(&left, parameters, arguments),
                describe_memory_range(&right, parameters, arguments)
            )
        }
    }
}

fn materialize_composite_resource_memory(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: CMemory,
) -> Result<CMemory, String> {
    let (memory, _) = instantiate_composite_resource_body_resources(
        name,
        composite_body,
        substitutions,
        parameters,
        arguments,
        memory,
    )?;
    Ok(memory)
}

fn instantiate_composite_resource_body_resources(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut memory: CMemory,
) -> Result<(CMemory, ResourceContext), String> {
    let mut resources = ResourceContext::new();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        let lowered =
            lower_resource_clause(&contained, parameters, arguments, &memory).map_err(|error| {
                format!(
                    "could not lower resource `{name}` contained `{}`: {}\n  {}",
                    describe_resource_clause(&contained),
                    error.message(),
                    describe_available_facts(&[], resources.facts(), parameters, arguments, &[])
                )
            })?;
        memory = materialize_composite_resource_cells(memory, &contained, &lowered, parameters);
        // This composite-body instantiation path has no fact assumptions yet.
        // Projection/packing paths check composition once assumptions are
        // available.
        resources = resources.unchecked_with_fact(lowered);
    }
    Ok((memory, resources))
}

fn resource_value_substitutions(
    definition: &ResourceDefinition,
    arguments: &[CValue],
) -> Result<BTreeMap<String, ContractExpression>, String> {
    if definition.parameters().len() != arguments.len() {
        return Err(format!(
            "resource `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            (
                parameter.name().to_string(),
                ContractExpression::CFragment(CExpression::Value(argument.clone())),
            )
        })
        .collect())
}

fn unfold_composite_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    step_index: usize,
) -> Result<CState, ClickError> {
    let definition = composite_resource_definition(
        resource_environment,
        resource,
        "unfold",
        claim_label,
        step_index,
    )?;
    let composite_body = definition
        .composite_body()
        .expect("composite_resource_definition should require a composite body");
    let substitutions =
        resource_argument_substitutions(definition, resource, claim_label, step_index)?;
    let abstract_resource = lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let resources = state
        .resources()
        .clone()
        .without_fact(&abstract_resource, &assumptions)
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `unfold({})` failed: {}",
                describe_resource_clause(resource),
                describe_missing_resource_fact(
                    &abstract_resource,
                    available_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    &[]
                )
            ))
        })?;
    state = state.with_resource_context(resources);

    for contained in composite_body.contains() {
        let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: could not instantiate `unfold({})`: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let lowered = lower_resource_clause(&contained, parameters, arguments, state.memory())?;
        let memory = materialize_composite_resource_cells(
            state.memory().clone(),
            &contained,
            &lowered,
            parameters,
        );
        let resources = state
            .resources()
            .clone()
            .try_compose_with_fact(lowered, &assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `unfold({})` produced {}",
                    describe_resource_clause(resource),
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        state = state.with_memory(memory).with_resource_context(resources);
    }

    for fact in composite_body.facts() {
        let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: could not instantiate `unfold({})` fact: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
        let lowered_fact = lower_outcome_proposition(
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_pure_facts,
            &fact,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: could not lower `unfold({})` pure fact `{}`: {message}\n{}",
                describe_resource_clause(resource),
                describe_click_proposition(&fact),
                describe_proof_context(
                    available_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    &[]
                )
            ))
        })?;
        available_pure_facts.push(lowered_fact);
    }

    append_state_resource_context_observable_facts(
        parameters,
        arguments,
        &state,
        available_pure_facts,
        &format!(
            "`{claim_label}` proof step {step_index}: `unfold({})`",
            describe_resource_clause(resource)
        ),
    )?;

    Ok(state)
}

fn fold_composite_resources_on_outcome(
    resource_environment: &ResourceEnvironment,
    resource_folds: &[ResourceClause],
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[ExecutionPureFact],
    available_pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    mut outcome: CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<CFunctionOutcome, ClickError> {
    for resource in resource_folds {
        let definition = composite_resource_definition(
            resource_environment,
            resource,
            "fold",
            claim_label,
            path_index,
        )?;
        let composite_body = definition
            .composite_body()
            .expect("composite_resource_definition should require a composite body");
        let substitutions =
            resource_argument_substitutions(definition, resource, claim_label, path_index)?;

        for fact in composite_body.facts() {
            let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            prove_ensure_proposition_by_simp(
                claim_label,
                path_index,
                execution_pure_facts,
                available_pure_facts,
                &fact,
                parameters,
                arguments,
                pre_state,
                &outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` fact failed: {}",
                    describe_resource_clause(resource),
                    error.message()
                ))
            })?;
        }

        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}\n  execution pure facts: {}",
                describe_resource_clause(resource),
                describe_function_outcome(&outcome, parameters, arguments),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        };
        let mut post_state = state;
        let assumptions = assumptions_from_propositions(available_pure_facts);
        for contained in composite_body.contains() {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let lowered =
                lower_resource_clause(&contained, parameters, arguments, post_state.memory())?;
            let resources = post_state
                .resources()
                .clone()
                .without_fact(&lowered, &assumptions)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` failed: {}",
                        describe_resource_clause(resource),
                        describe_missing_resource_fact(
                            &lowered,
                            available_pure_facts,
                            post_state.resources().facts(),
                            parameters,
                            arguments,
                            execution_pure_facts
                        )
                    ))
                })?;
            post_state = post_state.with_resource_context(resources);
        }

        let abstract_resource =
            lower_resource_clause(resource, parameters, arguments, post_state.memory())?;
        let resources = post_state
            .resources()
            .clone()
            .try_compose_with_fact(abstract_resource.clone(), &assumptions)
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` produced {}",
                    describe_resource_clause(resource),
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
        post_state = post_state.with_resource_context(resources);
        outcome = CFunctionOutcome::Return {
            value,
            state: post_state,
        };
    }

    Ok(outcome)
}

fn composite_resource_definition<'a>(
    resource_environment: &'a ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    claim_label: &str,
    step_index: usize,
) -> Result<&'a ResourceDefinition, ClickError> {
    let ResourceClause::Declared { name, .. } = resource else {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{action}` expects a composite resource"
        )));
    };
    if matches!(action, "fold" | "unfold")
        && !matches!(
            resource,
            ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                ..
            }
        )
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{action}` expects an owned composite resource"
        )));
    }
    if !matches!(
        resource,
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            ..
        }
    ) {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{action}` expects composite resource `{name}` to have a body"
        )));
    }
    let definition = resource_environment.get(name).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: unknown resource `{name}`"
        ))
    })?;
    if definition.composite_body().is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{action}` expects composite resource `{name}` to have a body"
        )));
    }
    Ok(definition)
}

fn resource_argument_substitutions(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    claim_label: &str,
    step_index: usize,
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    let ResourceClause::Declared {
        name,
        arguments,
        parameter_types,
        ..
    } = resource
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: expected declared resource"
        )));
    };
    if definition.name() != name {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: resource definition mismatch for `{name}`"
        )));
    }
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: resource `{name}` expects {} argument(s), got {}",
            definition.parameters().len(),
            arguments.len()
        )));
    }
    let expected_types = definition
        .parameters()
        .iter()
        .map(FunctionParameter::c_type)
        .collect::<Vec<_>>();
    if parameter_types != &expected_types {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: resource `{name}` has malformed argument type metadata"
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

fn instantiate_resource_clause(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

fn instantiate_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
    })
}

fn materialize_composite_resource_cells(
    mut memory: CMemory,
    resource_clause: &ResourceClause,
    lowered: &CResourceFact,
    parameters: &[syntax::C0Parameter],
) -> CMemory {
    let Some((segment, range)) = (match resource_clause {
        ResourceClause::Read(segment) => lowered.memory_view_range().map(|range| (segment, range)),
        ResourceClause::Write(segment) => lowered.memory_own_range().map(|range| (segment, range)),
        ResourceClause::Declared { .. } => None,
    }) else {
        return memory;
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (range.start(), range.end())
    else {
        return memory;
    };
    if end < start {
        return memory;
    }

    let element_width = contract_segment_element_width(parameters, segment);
    let base_memory = memory.clone();
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            range.base().clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        let load =
            Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(pointer.clone()));
        let value = match element_width {
            1 => CValue::UInt8(load),
            _ => CValue::Int32(load),
        };
        memory = memory.store(pointer, value);
    }
    memory
}

fn resolve_code_region_ref(
    function_block: &FunctionBlock,
    region_ref: &CodeRegionRef,
    claim_label: &str,
    step_index: usize,
) -> Result<CodeRegion, ClickError> {
    Ok(match region_ref {
        CodeRegionRef::Function => CodeRegion::Function,
        CodeRegionRef::Loop(index) => CodeRegion::Loop(*index),
        CodeRegionRef::Statement(index) => CodeRegion::Statement(*index),
        CodeRegionRef::Label(label) => *function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.label() == Some(label.as_str()))
            .map(StructuralClause::region)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: unknown code region label `{label}`"
                ))
            })?,
    })
}

fn validate_loop_code_region(
    parsed_function: &syntax::C0Function,
    loop_index: usize,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    if loop_index >= loop_count {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: function has no `loop({loop_index})` code region; it contains {loop_count} loop(s)"
        )));
    }
    Ok(())
}

fn validate_loop_vc_step(
    execution: &crate::kernel::SymbolicCExecution,
    loop_index: usize,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    let context_prefix = format!("loop {loop_index} ");
    let obligations = execution
        .paths()
        .iter()
        .flat_map(|path| path.obligations())
        .filter(|obligation| {
            obligation
                .context()
                .is_some_and(|context| context.starts_with(&context_prefix))
        })
        .cloned()
        .collect::<Vec<_>>();
    if !obligations.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `loop_vc(loop({loop_index}))` left obligations: {}",
            describe_obligations(&obligations)
        )));
    }
    Ok(())
}

fn validate_frame_code_region(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    code_region: Option<CodeRegion>,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    match code_region {
        None | Some(CodeRegion::Function) => {
            if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `frame()` proves function-level effect claims; use `frame(loop(N))` or a code region label to use loop effect summaries in an `ensures` proof"
                )));
            }
            Ok(())
        }
        Some(CodeRegion::Loop(loop_index)) => {
            validate_loop_code_region(parsed_function, loop_index, claim_label, step_index)?;
            if !function_block.structural_clauses().iter().any(|clause| {
                clause.region() == &CodeRegion::Loop(loop_index)
                    && clause.items().iter().any(StructuralItem::is_effect_kind)
            }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `frame(loop({loop_index}))` needs a loop effect clause such as `mutable` or `immutable`"
                )));
            }
            Ok(())
        }
        Some(CodeRegion::Statement(statement_index)) => {
            let statement_count = count_statements(parsed_function.body());
            if statement_index >= statement_count {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: function has no `statement({statement_index})` code region; it contains {statement_count} statement(s)"
                )));
            }
            Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `frame(statement({statement_index}))` is not supported yet"
            )))
        }
    }
}

fn validate_function_frame_step(
    execution: &crate::kernel::SymbolicCExecution,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    step_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    requirement_pure_facts: &[Proposition],
) -> Result<(), ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `frame()` hit execution limit {limit:?}"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `frame()` had no complete execution path"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `frame()` failed on path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    requirement_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    path.facts()
                )
            )));
        }
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `frame()` saw unexpected theorem body {proposition:?}\n  execution pure facts: {}",
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };
        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_function_claim(
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            &outcome,
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
            &[],
        )?;
    }

    Ok(())
}

fn prove_claim_from_steps_execution(
    execution: &crate::kernel::SymbolicCExecution,
    execution_mode: ProofStepExecutionMode,
    source_path: &str,
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_pure_facts: &[Proposition],
    unfolded_predicates: &[String],
    theorem_applications: &[(usize, TheoremApplication)],
    resource_folds: &[ResourceClause],
    use_simp: bool,
    proof_steps: &[ProofStep],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`proof steps` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`proof steps` could not prove any complete execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`proof steps` failed for `{claim_label}` path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    requirement_pure_facts,
                    state.resources().facts(),
                    parameters,
                    arguments,
                    path.facts()
                )
            )));
        }
        let mut outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`proof steps` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  pure facts: {}\n  execution pure facts: {}",
                    describe_pure_facts(requirement_pure_facts),
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        path_requirements = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &path_requirements,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`proof steps` failed for `{claim_label}` path {path_index}: {message}"
            ))
        })?;
        outcome = fold_composite_resources_on_outcome(
            resource_environment,
            resource_folds,
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            parameters,
            arguments,
            state,
            outcome,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )?;
        path_requirements = project_outcome_resource_facts(
            resource_environment,
            parameters,
            arguments,
            state,
            &outcome,
            &path_requirements,
            predicate_environment,
            click_function_environment,
            claim_label,
            path_index,
        )?;
        if !theorem_applications.is_empty() {
            let CFunctionOutcome::Return {
                value: result,
                state: post_state,
            } = &outcome
            else {
                return Err(ClickError::new(format!(
                    "`proof steps` failed for `{claim_label}` path {path_index}: theorem application requires a return outcome, got {}\n  execution pure facts: {}",
                    describe_function_outcome(&outcome, parameters, arguments),
                    describe_execution_pure_facts(path.facts())
                )));
            };
            let values = parameter_values(parameters, arguments).map_err(|error| {
                ClickError::new(format!(
                    "`proof steps` failed for `{claim_label}` path {path_index}: {}",
                    error.message
                ))
            })?;
            let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
            let application_context = TheoremApplicationContext {
                values: &values,
                array_refs: &array_refs,
                pre_state: state,
                post_state,
                result: Some(result),
            };
            path_requirements = apply_theorem_applications_to_available(
                theorem_environment,
                theorem_applications,
                claim_label,
                Some(path_index),
                path_requirements,
                &application_context,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )?;
        }
        let mut checking_requirements = path_requirements.clone();
        let has_existence_steps = proof_steps
            .iter()
            .any(|step| matches!(step, ProofStep::Witness(_) | ProofStep::Choose(_)));
        if has_existence_steps {
            check_function_claim_with_existence_steps(
                claim_label,
                path_index,
                path.facts(),
                &mut checking_requirements,
                claim,
                parameters,
                arguments,
                state,
                &outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                proof_steps,
                function_block.requires(),
                use_simp,
            )?;
        } else {
            if use_simp {
                check_function_claim_by_simp(
                    claim_label,
                    path_index,
                    path.facts(),
                    &path_requirements,
                    claim,
                    parameters,
                    arguments,
                    state,
                    &outcome,
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                )?;
            } else {
                check_function_claim(
                    claim_label,
                    path_index,
                    path.facts(),
                    &path_requirements,
                    claim,
                    parameters,
                    arguments,
                    state,
                    &outcome,
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                )?;
            }
        }
        let specification = c_function_specification(
            state.clone(),
            arguments.to_vec(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = match execution_mode {
            ProofStepExecutionMode::Verification => {
                prove_c_function_satisfies_specification_from_symbolic_path(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    path.facts(),
                    path.obligations(),
                )
            }
            ProofStepExecutionMode::Bounded => {
                prove_c_function_satisfies_specification_with_environment(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    function_environment.clone(),
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`proof steps` failed for `{claim_label}` path {path_index}: bounded execution did not satisfy the packaged specification\n  pure facts: {}\n  execution pure facts: {}",
                        describe_pure_facts(&specification.requires()),
                        describe_execution_pure_facts(path.facts())
                    ))
                })?
            }
        };

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind: ProofKind::ProofSteps,
            proof_steps: Some(proof_steps.to_vec()),
            specification,
            theorem,
        });
    }

    Ok(verified)
}

enum AutoExecutionKind<'a> {
    Frame,
    LoopVerification,
    BoundedExecution {
        environment: &'a CFunctionEnvironment,
    },
}

impl AutoExecutionKind<'_> {
    fn proof_kind(&self) -> ProofKind {
        match self {
            Self::Frame => ProofKind::Frame,
            Self::LoopVerification => ProofKind::LoopVerification,
            Self::BoundedExecution { .. } => ProofKind::BoundedExecution,
        }
    }

    fn tactic_name(&self) -> &'static str {
        match self {
            Self::Frame => "frame",
            Self::LoopVerification | Self::BoundedExecution { .. } => "auto",
        }
    }
}

fn with_proof_steps(
    mut theorems: Vec<VerifiedCTheorem>,
    proof_steps: Option<Vec<ProofStep>>,
) -> Vec<VerifiedCTheorem> {
    if let Some(proof_steps) = proof_steps {
        for theorem in &mut theorems {
            theorem.proof_steps = Some(proof_steps.clone());
        }
    }
    theorems
}

fn requirements_with_structural_unfolds(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_block: &FunctionBlock,
    requirement_pure_facts: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    let unfolded_predicates = structural_unfold_step_names(function_block);
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        requirement_pure_facts,
    )
}

fn structural_unfold_step_names(function_block: &FunctionBlock) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for clause in function_block.structural_clauses() {
        for item in clause.items() {
            for name in item.proof().unfold_step_names() {
                if seen.insert(name.clone()) {
                    names.push(name);
                }
            }
        }
    }
    names
}

fn certified_proof_steps(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    candidates: Vec<Vec<ProofStep>>,
) -> Option<Vec<ProofStep>> {
    candidates.into_iter().find(|steps| {
        prove_claim_by_steps(
            source_path,
            function_block,
            parsed_function,
            claim,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            steps,
        )
        .is_ok()
    })
}

fn frame_proof_step_candidates() -> Vec<Vec<ProofStep>> {
    vec![vec![ProofStep::SymbolicExecute, ProofStep::Frame(None)]]
}

fn bounded_execution_proof_step_candidates(claim: &FunctionClaimRef<'_>) -> Vec<Vec<ProofStep>> {
    match claim {
        FunctionClaimRef::Ensure(_, _) => vec![
            vec![ProofStep::BoundedExecute, ProofStep::Simp],
            vec![ProofStep::BoundedExecute],
        ],
        FunctionClaimRef::Effect(_, _) => {
            vec![vec![ProofStep::BoundedExecute, ProofStep::Frame(None)]]
        }
    }
}

fn auto_loop_verification_proof_step_candidates(
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
) -> Vec<Vec<ProofStep>> {
    let mut base = vec![ProofStep::SymbolicExecute];
    base.extend(
        loop_step_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofStep::LoopVc(CodeRegionRef::Loop(loop_index))),
    );
    base.extend(
        loop_effect_summary_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofStep::Frame(Some(CodeRegionRef::Loop(loop_index)))),
    );

    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            let mut simp = base.clone();
            simp.push(ProofStep::Simp);

            let direct = base;
            vec![simp, direct]
        }
        FunctionClaimRef::Effect(_, _) => {
            let mut frame = base.clone();
            frame.push(ProofStep::Frame(None));

            let direct = base;
            vec![frame, direct]
        }
    }
}

fn loop_step_regions(function_block: &FunctionBlock) -> BTreeSet<usize> {
    function_block
        .structural_clauses()
        .iter()
        .filter_map(|clause| match clause.region() {
            CodeRegion::Loop(index) => Some(*index),
            CodeRegion::Function | CodeRegion::Statement(_) => None,
        })
        .collect()
}

fn loop_effect_summary_regions(function_block: &FunctionBlock) -> BTreeSet<usize> {
    function_block
        .structural_clauses()
        .iter()
        .filter_map(|clause| match clause.region() {
            CodeRegion::Loop(index)
                if clause.items().iter().any(StructuralItem::is_effect_kind) =>
            {
                Some(*index)
            }
            _ => None,
        })
        .collect()
}

fn execution_obligation_error(
    execution: &crate::kernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ClickError> {
    execution_obligation_error_for_tactic(
        "auto",
        execution,
        ensure_label,
        requirement_pure_facts,
        resource_facts,
        parameters,
        arguments,
    )
}

fn execution_obligation_error_for_tactic(
    tactic_name: &str,
    execution: &crate::kernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_pure_facts: &[Proposition],
    resource_facts: &[CResourceFact],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ClickError> {
    if let Some(limit) = execution.limit() {
        return Some(ClickError::new(format!(
            "`{tactic_name}` hit execution limit {limit:?} for `{ensure_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Some(ClickError::new(format!(
            "`{tactic_name}` could not prove any complete execution path for `{ensure_label}`"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Some(ClickError::new(format!(
                "`{tactic_name}` failed for `{ensure_label}` path {path_index}: {}",
                describe_missing_proof_obligations(
                    path.obligations(),
                    requirement_pure_facts,
                    resource_facts,
                    parameters,
                    arguments,
                    path.facts()
                )
            )));
        }
    }

    None
}

fn prove_claim_from_execution(
    execution: &crate::kernel::SymbolicCExecution,
    execution_kind: AutoExecutionKind<'_>,
    source_path: &str,
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_pure_facts: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let proof_kind = execution_kind.proof_kind();
    let tactic_name = execution_kind.tactic_name();
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{tactic_name}` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{tactic_name}` could not prove any complete execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`{tactic_name}` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  pure facts: {}\n  execution pure facts: {}",
                    describe_pure_facts(&requirement_pure_facts),
                    describe_execution_pure_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_pure_facts.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        path_requirements = project_outcome_resource_facts(
            resource_environment,
            parameters,
            arguments,
            state,
            &outcome,
            &path_requirements,
            predicate_environment,
            click_function_environment,
            claim_label,
            path_index,
        )?;
        check_function_claim(
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            &outcome,
            predicate_environment,
            click_function_environment,
            &[],
        )?;
        let path_requirements_description = describe_pure_facts(&path_requirements);
        let specification = c_function_specification(
            state.clone(),
            arguments.to_vec(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = match execution_kind {
            AutoExecutionKind::Frame | AutoExecutionKind::LoopVerification => {
                prove_c_function_satisfies_specification_from_symbolic_path(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    path.facts(),
                    path.obligations(),
                )
            }
            AutoExecutionKind::BoundedExecution { environment } => {
                prove_c_function_satisfies_specification_with_environment(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    (*environment).clone(),
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`auto` failed for `{claim_label}` path {path_index}: execution did not satisfy the packaged specification\n  pure facts: {}\n  execution pure facts: {}",
                        path_requirements_description,
                        describe_execution_pure_facts(path.facts())
                    ))
                })?
            }
        };

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind,
            proof_steps: None,
            specification,
            theorem,
        });
    }

    Ok(verified)
}
