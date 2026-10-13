//! Explicit theorem execution uses the ordinary grouped C proof and its
//! checked execution artifacts. Only the final contract implication is new.
use super::*;
use crate::surface::verification::{
    substitute_contract_segment, substitute_resource_clause_for_summary_in,
};

fn substitute_requirement(
    r: &Requirement,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<Requirement, String> {
    Ok(match r {
        Requirement::Proposition(p) => {
            Requirement::Proposition(substitute_click_proposition_in(p, substitutions)?)
        }
        Requirement::Resource(r) => {
            Requirement::Resource(substitute_resource_clause_for_summary_in(r, substitutions)?)
        }
        Requirement::LoadableSegment { segment } => Requirement::LoadableSegment {
            segment: substitute_contract_segment(segment, substitutions)?,
        },
    })
}

pub(super) fn verify_execution_theorem(
    theorem: &TheoremDefinition,
    spec_definitions: SpecDefinitions<'_>,
    theorems: &TheoremEnvironment,
    environment: Option<&CExecutionEnvironment>,
    resources: &ResourceEnvironment,
    function_source_registry: std::sync::Arc<FunctionSourceRegistry>,
) -> Result<VerifiedPureTheorem, ClickError> {
    let execution = theorem.executes.as_ref().expect("execution declaration");
    let error = |message: &str| {
        ClickError::new(format!("theorem `{}` executes: {message}", theorem.name()))
            .at_declaration(theorem.name())
    };
    let environment = environment.ok_or_else(|| error("requires a C contract environment"))?;
    let [ensure] = theorem.ensures() else {
        return Err(error("requires exactly one target-contract conclusion"));
    };
    let Ensure::Proposition(
        goal @ ClickProposition::PredicateCall {
            name: target_name,
            arguments,
        },
    ) = ensure.ensure()
    else {
        return Err(error(
            "the conclusion must be a contract for the executed callback",
        ));
    };
    // The conclusion chooses the form. A function address executes that named
    // project function and has no source premises; a plain binding executes
    // the theorem's arbitrary callback parameter under its source contracts.
    let concrete_callee = match arguments.as_slice() {
        [argument] => contract_expression_function_address(argument),
        _ => None,
    };
    if !theorem.type_parameters().is_empty() {
        return Err(error("an execution theorem takes no type parameters"));
    }
    let callback = match concrete_callee {
        Some(callee) => {
            if callee != execution.callback {
                return Err(error("the conclusion must describe the executed function"));
            }
            if !theorem.parameters().is_empty() {
                return Err(error(
                    "a concrete execution theorem takes no theorem parameters",
                ));
            }
            if !theorem.requires().is_empty() {
                return Err(error(
                    "a concrete execution theorem has no source-contract premises; its source is the executed function's own contract",
                ));
            }
            None
        }
        None => {
            let [callback] = theorem.parameters() else {
                return Err(error("requires exactly one callback theorem parameter"));
            };
            if callback.name() != execution.callback {
                return Err(error(
                    "the executed callback must be the theorem's function-pointer parameter",
                ));
            }
            Some(callback)
        }
    };
    let concrete_callee =
        concrete_callee.map(|name| spec_definitions.predicates.function_execution_name(name));
    let call_name = concrete_callee.unwrap_or(&execution.callback);
    let mut names = BTreeSet::from([execution.callback.clone()]);
    for parameter in &execution.parameters {
        if !names.insert(parameter.name().to_string()) || parameter.name() == "result" {
            return Err(error(
                "call argument names must be distinct from each other, the callback, and result",
            ));
        }
    }
    let is_callback = |arguments: &[ContractExpression]| {
        matches!(arguments, [ContractExpression::Binding(name)] if name == &execution.callback)
            || matches!(arguments, [ContractExpression::CFragment(CExpression::Variable(name))] if name == &execution.callback)
    };
    if concrete_callee.is_none() && !is_callback(arguments) {
        return Err(error("the conclusion must describe the executed callback"));
    }
    let target = spec_definitions
        .predicates
        .contract_definition(target_name)
        .ok_or_else(|| error("the conclusion must name a function contract"))?;
    let mut source_names = Vec::new();
    if let Some(callback) = callback {
        if callback.name() == "result"
            && target.function_block().signature().return_type() != C0Type::Void
        {
            return Err(error(
                "a return-valued callback parameter must not be named result",
            ));
        }
        if theorem.requires().is_empty() {
            return Err(error("requires at least one source-contract assumption"));
        }
        for requirement in theorem.requires() {
            let Some(ClickProposition::PredicateCall { name, arguments }) =
                requirement.proposition()
            else {
                return Err(error(
                    "requires a source-contract assumption for the executed callback",
                ));
            };
            let source = spec_definitions
                .predicates
                .contract_definition(name)
                .ok_or_else(|| error("the source assumption must name a function contract"))?;
            if !is_callback(arguments) {
                return Err(error(
                    "the source assumption must describe the executed callback",
                ));
            }
            if callback.c_type() != source.function_pointer_type() {
                return Err(error(
                    "executes signature does not match the source contract",
                ));
            }
            source_names.push(name.as_str());
        }
    }
    // A concrete callee is called as ordinary C, so the written parameter list
    // is checked against the signature the call rule will use as well as
    // against the target contract's interface.
    if let Some(callee) = concrete_callee {
        let (parameter_types, return_type) =
            crate::kernel::c_project_function_signature(environment, callee).ok_or_else(|| {
                error(&format!(
                    "`{callee}` is not a verified or external function in this project"
                ))
            })?;
        if parameter_types.len() != execution.parameters.len()
            || execution
                .parameters
                .iter()
                .zip(&parameter_types)
                .any(|(written, declared)| &written.c_type().to_kernel_type() != declared)
            || target
                .function_block()
                .signature()
                .return_type()
                .to_kernel_type()
                != return_type
        {
            return Err(error(&format!(
                "the executes parameter list does not match the C signature of `{callee}`"
            )));
        }
    }
    if callback.is_some_and(|callback| callback.c_type() != target.function_pointer_type())
        || execution.parameters.len() != target.function_block().signature().parameters().len()
        || execution
            .parameters
            .iter()
            .zip(target.function_block().signature().parameters())
            .any(|(written, declared)| {
                written.c_type() != declared.c_type()
                    || written.struct_name() != declared.struct_name()
                    || written.pointee_is_constant() != declared.pointee_is_constant()
                    || written.is_reference() != declared.is_reference()
            })
    {
        return Err(error(
            "executes signature does not match the callback and target contract",
        ));
    }
    let SourceProof::Script(tactics) = ensure.proof() else {
        return Err(error("requires an explicit execution proof block"));
    };
    let values = target
        .function_block()
        .signature()
        .parameters()
        .iter()
        .zip(&execution.parameters)
        .map(|(declared, written)| {
            (
                declared.name().to_string(),
                ContractExpression::CFragment(CExpression::Variable(written.name().to_string())),
            )
        })
        .collect::<BTreeMap<_, _>>();
    // The conclusion's `as` map is the only way a target proof parameter is
    // named inside the block, so the target's clauses are rewritten to those
    // names before anything reads them. Goals, ambient facts, diagnostics, and
    // expanded proofs then agree with what the proof script may write.
    let mut instance_renames = BTreeMap::new();
    let declared_parameters = target.proof_parameters().unwrap_or_default();
    if declared_parameters.len() != execution.target_instances().len() {
        return Err(error(
            "the conclusion must introduce one name per target proof parameter",
        ));
    }
    for (declared, (parameter, introduced)) in
        declared_parameters.iter().zip(execution.target_instances())
    {
        let ResourceClause::Named { binding, resource } = declared else {
            return Err(error("a target proof parameter must be a named instance"));
        };
        let ResourceClause::Declared { .. } = resource.as_ref() else {
            return Err(error(
                "a target proof parameter must name a declared resource",
            ));
        };
        if &binding.name != parameter {
            return Err(error(
                "the conclusion's instance map does not match the target proof parameters",
            ));
        }
        instance_renames.insert(
            parameter.clone(),
            InstanceRename {
                name: introduced.clone(),
                identity: binding.identity,
            },
        );
    }
    let substitutions = ContractSubstitutions::with_instance_renames(&values, &instance_renames);
    let mut block = target.function_block().clone();
    block.one_call_proof = true;
    block.signature.name = theorem.name().to_string();
    block.signature.parameters = execution.parameters.clone();
    if let Some(callback) = callback {
        block.signature.parameters.push(callback.clone());
    }
    block.requires = block
        .requires
        .iter()
        .map(|r| substitute_requirement(r, &substitutions))
        .collect::<Result<_, _>>()
        .map_err(ClickError::new)?;
    block.requires.extend(theorem.requires().iter().cloned());
    for clause in &mut block.ensures {
        clause.ensure = match &clause.ensure {
            Ensure::Proposition(p) => Ensure::Proposition(
                substitute_click_proposition_in(p, &substitutions).map_err(ClickError::new)?,
            ),
            Ensure::Resource(r) => Ensure::Resource(
                substitute_resource_clause_for_summary_in(r, &substitutions)
                    .map_err(ClickError::new)?,
            ),
        };
    }
    block.grouped_proof = Some(ensure.proof().clone());
    let arguments = execution
        .parameters
        .iter()
        .map(|p| syntax::C0Expression::Variable(p.name().to_string()))
        .collect();
    let body = if block.signature().return_type() == C0Type::Void {
        syntax::C0Statement::Call {
            function_name: call_name.to_string(),
            arguments,
            site: crate::languages::c::syntax::C0Site::NONE,
        }
    } else {
        syntax::C0Statement::Seq(
            Box::new(syntax::C0Statement::CallAssign {
                target: "result".into(),
                function_name: call_name.to_string(),
                arguments,
                site: crate::languages::c::syntax::C0Site::NONE,
            }),
            Box::new(syntax::C0Statement::Return(
                syntax::C0Expression::Variable("result".into()),
                crate::languages::c::syntax::C0Site::NONE,
            )),
        )
    };
    let parsed = crate::surface::verification::external_c0_function(&block).with_proof_body(body);
    // The wrapper may rename parameters, but calls forward them in the
    // already-checked order. Retain the target contract's actual requirements
    // rather than deriving stronger inputs from the callee's signature.
    let target_interface = environment
        .get_function_contract(target_name)
        .ok_or_else(|| error("the target contract has no lowered interface"))?
        .interface();
    let function = parsed
        .to_kernel_function()
        .with_typed_access_policy(target_interface.typed_access_policy())
        .with_native_span_expression_inputs(
            target_interface.native_span_expression_inputs().to_vec(),
        )
        .with_native_span_inputs(target_interface.native_span_inputs().to_vec())
        .with_scalar_object_inputs(target_interface.scalar_object_inputs().to_vec())
        .with_aggregate_object_inputs(target_interface.aggregate_object_inputs().to_vec());
    let parsed = parsed.with_prelowered_kernel_function(function);
    let claims = function_claims(&block);
    let verified = prove_claims_by_grouped_script(
        None,
        "",
        &block,
        &parsed,
        &claims,
        environment,
        spec_definitions,
        resources,
        theorems,
        function_source_registry,
        tactics,
    )?;
    // Certification starts from the entry the proof was built from.
    let (mut state, arguments, facts) = match verified
        .iter()
        .find_map(|verified| verified.entry_context.clone())
    {
        Some(entry) => (
            entry.state.clone(),
            entry.arguments.clone(),
            entry.pure_facts.clone(),
        ),
        None => {
            let (state, arguments, facts, _) = initial_claim_context(
                &block,
                &parsed,
                resources,
                spec_definitions,
                theorem.name(),
            )?;
            (state, arguments, facts)
        }
    };
    // A stable-view proof artifact carries the exact caller state the checked
    // function-entry boundary accepted, including its loan ledger roots and
    // resource occurrence IDs. Certifying the one-call proof against an
    // independently built entry state would compare two equivalent-looking
    // but distinct authorities and reject every artifact. This is the same
    // reuse the ordinary contract-certification path performs.
    if let Some(entry) = verified
        .iter()
        .find_map(|verified| verified.checked_execution.caller_state())
    {
        state = entry.clone();
    }
    let function = annotated_function_with_assumptions(
        &block,
        &parsed,
        &state,
        &arguments,
        spec_definitions,
        resources,
        Some(ResourceFrameEntry {
            assumptions: &assumptions_from_propositions(&facts),
            checked_entry_state: None,
        }),
    )?;
    let artifacts = crate::surface::verification::distinct_checked_executions(&verified)
        .into_iter()
        .map(|execution| CCheckedFunctionExecution::clone(execution))
        .collect::<Vec<_>>();
    let execution =
        prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems(
            state,
            function.clone(),
            arguments,
            environment.clone(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            CFunctionContractExecutionMode::VerifyLoops,
            &artifacts,
            &[],
        );
    let propositions = verified
        .iter()
        .filter_map(|v| v.checked_proposition.clone())
        .collect::<Vec<_>>();
    let claims = c_verified_function_contract_claims_with_checked_propositions(
        &function,
        &execution,
        &propositions,
    )
    .ok_or_else(|| error("the one-call proof did not certify every target obligation"))?;
    let rule = c_verified_function_rule(function, &claims)
        .ok_or_else(|| error("the one-call proof did not establish a checked contract"))?;
    let context = pure_theorem_context(theorem, spec_definitions)?;
    let conclusion = lower_pure_theorem_proposition(
        theorem.name(),
        goal,
        &context.values,
        &context.array_refs,
        &context.memory,
        spec_definitions,
    )
    .map_err(ClickError::new)?;
    let authority = match concrete_callee {
        Some(callee) => crate::kernel::prove_executed_concrete_contract_refinement(
            environment,
            callee,
            target_name,
            conclusion.clone(),
            &rule,
        ),
        None => crate::kernel::prove_executed_contract_refinement(
            environment,
            &source_names,
            target_name,
            conclusion.clone(),
            &rule,
        ),
    }
    .ok_or_else(|| {
        error("the checked call does not establish the declared contract implication")
    })?;
    let certificate = verified
        .first()
        .ok_or_else(|| error("missing execution proof"))?
        .expanded_proof_certificate()?;
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index: 0,
        ensure_clause: ensure.clone(),
        proof_kind: ProofKind::TacticScript,
        proof: Some(certificate),
        requires: context.requires,
        conclusion,
        kernel_authority: Some(authority),
        checked_completion: None,
    })
}
