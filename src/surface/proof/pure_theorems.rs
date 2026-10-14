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

/// A theorem's `requires` clauses as the propositions they state, in source
/// order.
///
/// Every consumer of a theorem's premises reads them through here — its own
/// proof setup, its induction hypothesis, and each of the three places an
/// application is checked — so a `views` range is one premise in one position
/// wherever it is read, and `requirement N` means the same clause to all of
/// them.
pub(in crate::surface) fn theorem_requirement_propositions(
    theorem: &TheoremDefinition,
) -> Result<Vec<ClickProposition>, ClickError> {
    theorem
        .requires()
        .iter()
        .map(|requirement| {
            requirement.theorem_proposition().ok_or_else(|| {
                ClickError::new(crate::surface::validation::theorem_resource_clause_refusal(
                    theorem.name(),
                ))
            })
        })
        .collect()
}

/// Proves `theorem_definitions` in order. Each proof may apply the theorems of
/// `dependencies` and the definitions before it. Dependencies are declarations
/// proved elsewhere, such as the standard library, and are not re-proved here.
pub(in crate::surface) fn verify_theorem_definitions(
    dependencies: TheoremEnvironment,
    theorem_definitions: &[TheoremDefinition],
    spec_definitions: SpecDefinitions<'_>,
    function_environment: Option<&CExecutionEnvironment>,
    resource_environment: &ResourceEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = dependencies;
    for theorem in theorem_definitions {
        crate::surface::enter_ambient_declaration(theorem.name());
        #[cfg(test)]
        PROVED_THEOREMS.with(|proved| proved.borrow_mut().push(theorem.name().to_string()));
        if theorem.executes.is_some() {
            verified.push(
                verify_execution_theorem(
                    theorem,
                    spec_definitions,
                    &theorem_environment,
                    function_environment,
                    resource_environment,
                    function_source_registry.clone(),
                )
                .map_err(ClickError::located_by_ambient_source)?,
            );
            theorem_environment.insert(clone_theorem_definition_iteratively(theorem));
            continue;
        }
        let started = std::time::Instant::now();
        verified.extend(
            crate::instrumentation::with_default_tactic_limits(|| {
                verify_theorem_definition(
                    theorem,
                    spec_definitions,
                    &theorem_environment,
                    function_environment,
                )
            })
            .map_err(ClickError::located_by_ambient_source)?,
        );
        crate::instrumentation::emit(
            crate::instrumentation::VerificationEvent::FunctionFinished {
                name: theorem.name().to_owned(),
                elapsed: started.elapsed(),
            },
        );
        theorem_environment.insert(clone_theorem_definition_iteratively(theorem));
    }
    Ok(verified)
}

/// Verifies one theorem, generic or not. A theorem with type parameters is
/// checked once at rigid types, each parameter standing for an arbitrary
/// type; that is the form [`verify_concrete_theorem_definition`] takes.
pub(in crate::surface) fn verify_theorem_definition(
    theorem: &TheoremDefinition,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    if theorem.type_parameters().is_empty() {
        return verify_concrete_theorem_definition(
            theorem,
            spec_definitions,
            theorem_environment,
            function_environment,
        );
    }
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
    let mut symbolic =
        generics::instantiate_theorem(theorem, &substitution).map_err(ClickError::new)?;
    symbolic.name = theorem.name().to_string();
    verify_concrete_theorem_definition(
        &symbolic,
        spec_definitions,
        theorem_environment,
        function_environment,
    )
}

pub(in crate::surface) fn verify_concrete_theorem_definition(
    theorem: &TheoremDefinition,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    debug_assert!(theorem.type_parameters().is_empty());
    let context = pure_theorem_context(theorem, spec_definitions)?;
    theorem
        .ensures()
        .iter()
        .enumerate()
        .map(|(ensure_index, ensure_clause)| {
            let claim_label = theorem.ensure_claim_label(ensure_index);
            let started = std::time::Instant::now();
            let result = verify_theorem_ensure(
                theorem,
                ensure_index,
                ensure_clause,
                &claim_label,
                &context,
                spec_definitions,
                theorem_environment,
                function_environment,
            );
            if result.is_ok() {
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::ProofClaimFinished {
                        function: theorem.name().to_owned(),
                        claim: claim_label,
                        elapsed: started.elapsed(),
                    },
                );
            }
            result
        })
        .collect()
}

#[derive(Clone, Debug)]
pub(super) struct PureTheoremContext {
    /// Immutable specification parameter names, retained for diagnostics.
    pub(super) diagnostic_names: std::sync::Arc<[(Variable, String)]>,
    pub(super) declaration_bindings: BTreeMap<String, ContractExpression>,
    pub(super) memory: CMemory,
    pub(super) values: BTreeMap<String, CValue>,
    pub(super) integer_values:
        crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    pub(super) array_refs: ClickArrayRefs,
    pub(super) requires: Vec<Proposition>,
    pub(super) surface_requirements: SurfacePropositionMap,
}

impl PureTheoremContext {
    fn with_declaration_bindings(
        &self,
        bindings: &[(String, Option<ClickType>, ContractExpression)],
        spec_definitions: SpecDefinitions<'_>,
    ) -> Result<Self, ClickError> {
        let mut context = self.clone();
        let names: BTreeSet<_> = bindings
            .iter()
            .flat_map(|(_, _, value)| contract_expression_referenced_names(value))
            .collect();
        let mut substitutions = BTreeMap::new();
        for name in names {
            if let Some(value) = self.values.get(&name) {
                substitutions.insert(
                    name.clone(),
                    ContractExpression::CFragment(CExpression::Value(value.clone())),
                );
            } else if let Some(value) = self.integer_values.get(&name) {
                // This spelling cannot be written by a source-level binder.
                let captured = format!("@declaration:{name}");
                context.integer_values = context
                    .integer_values
                    .with_inserted(captured.clone(), value.clone());
                substitutions.insert(name, ContractExpression::Binding(captured));
            }
        }
        let assumptions = assumptions_from_propositions(&context.requires);
        for (name, click_type, value) in bindings {
            let value =
                substitute_contract_expression(value, &substitutions).map_err(ClickError::new)?;
            let promoted = super::surface_lowering::promote_integer_expression(
                &value,
                &context.integer_values,
                &crate::persistent::PersistentMap::default(),
            );
            let is_integer = match click_type.as_ref() {
                Some(ClickType::Integer) => true,
                Some(_) => false,
                None => contract_expression_referenced_names(&promoted)
                    .iter()
                    .any(|name| context.integer_values.get(name).is_some()),
            };
            let value = if is_integer {
                let value = match crate::surface::lowering::lower_contract_integer_to_spec(
                    &promoted,
                    &context.integer_values,
                ) {
                    Ok(value) => value,
                    Err(_) => {
                        // Conversion-backed and function-backed aliases also
                        // need shared terms. Inlining their source expressions
                        // would double a binary alias chain at every binding.
                        let state = CState::new().with_memory(context.memory.clone());
                        let integer_values = contract_expression_referenced_names(&promoted)
                            .into_iter()
                            .filter_map(|name| {
                                context
                                    .integer_values
                                    .get(&name)
                                    .map(|value| (name, value.clone()))
                            })
                            .fold(
                                crate::persistent::PersistentMap::default(),
                                |values, (name, value)| values.with_inserted(name, value),
                            );
                        let spec = crate::surface::lowering::elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
                            &ClickProposition::Comparison {
                                left: promoted,
                                operator: ComparisonOperator::Equal,
                                right: ContractExpression::IntegerLiteral("0".into()),
                            }, BTreeMap::new(), BTreeMap::new(), &state, BTreeMap::new(), BTreeMap::new(),
                            BTreeMap::new(), &integer_values, None, &RecordedSnapshots::new(), spec_definitions,
                            BTreeSet::new(), BTreeMap::new(),).map_err(ClickError::new)?;
                        let crate::kernel::SpecProposition::IntegerComparison { left, .. } = spec
                        else {
                            // An unannotated machine conversion can reference
                            // Integer inputs without having an Integer result.
                            // Keep its typed expression rather than narrowing it.
                            if click_type.as_ref() == Some(&ClickType::Integer) {
                                return Err(ClickError::new(
                                    "declaration alias must be an Integer expression",
                                ));
                            }
                            substitutions.insert(name.clone(), value.clone());
                            context.declaration_bindings.insert(name.clone(), value);
                            continue;
                        };
                        let term = crate::kernel::capture_spec_integer_value(&state, &left, Some(&state), &assumptions)
                            .map_err(|refusal| ClickError::new(crate::surface::proof_diagnostics::render::describe_spec_capture_refusal(&refusal)))?;
                        crate::kernel::SpecIntegerExpression::Term(term)
                    }
                };
                let captured = format!("@declaration:{name}");
                context.integer_values = context
                    .integer_values
                    .with_inserted(captured.clone(), value);
                ContractExpression::Binding(captured)
            } else {
                value
            };
            substitutions.insert(name.clone(), value.clone());
            context.declaration_bindings.insert(name.clone(), value);
        }
        Ok(context)
    }
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
                for arm in proof_cases.arms() {
                    collect_structural_induction_arguments(arm.tactics(), hypothesis, collected);
                }
            }
            _ => {}
        }
    }
}

pub(super) fn pure_induction_hypothesis(
    setup: &PureInductionSetup,
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, ClickError> {
    let Some(CValue::Int32(Bitvector32Term::Variable(current_variable))) =
        context.values.get(&setup.parameter)
    else {
        return Err(ClickError::new("invalid int32 induction parameter"));
    };
    // Lower the hypothesis in its own requirement scope. These premises
    // are retained below as implications, so definedness is never granted
    // to an application that does not establish the smaller argument's guards.
    let mut assumptions = PureFactContext::new();
    let mut opaque_requirements = Vec::new();
    for requirement in &setup.surface_requires {
        let lowered = lower_pure_theorem_proposition_opaque(
            &setup.hypothesis,
            requirement,
            &assumptions,
            ContractEnvironment::new(&context.values, &context.array_refs),
            &context.memory,
            spec_definitions,
        )
        .map_err(ClickError::new)?;
        assumptions = assumptions.assume_proposition(lowered.clone());
        opaque_requirements.push(lowered);
    }
    let opaque_goal = lower_pure_theorem_proposition_opaque(
        &setup.hypothesis,
        &setup.surface_goal,
        &assumptions,
        ContractEnvironment::new(&context.values, &context.array_refs),
        &context.memory,
        spec_definitions,
    )
    .map_err(ClickError::new)?;
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
        // The hypothesis is the theorem's own statement at the smaller
        // argument, and the theorem's statement includes the byte-count
        // guards of every range it names: its proof assumed them, and anyone
        // who applies it owes them. Substituting the argument moves the range,
        // so the guards are recomputed for the moved range and become
        // premises of the hypothesis. Without them the hypothesis would be
        // strictly stronger than the theorem it is proving — it would grant
        // the conclusion at an argument where the range's extent wraps, which
        // is an argument the theorem itself never covered.
        for guard in crate::kernel::stated_loadable_extent_guards(&requirement)
            .into_iter()
            .rev()
        {
            body = Proposition::Implies(Box::new(guard), Box::new(body));
        }
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
    let surface_requires = theorem_requirement_propositions(theorem)?;

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
                    ensuring: proof_if.ensuring.clone(),
                    then_tactics: transform(&proof_if.then_tactics, hypothesis)?,
                    else_tactics: transform(&proof_if.else_tactics, hypothesis)?,
                })),
                ProofTactic::Both(both) => Ok(ProofTactic::Both(ProofBoth {
                    left_tactics: transform(&both.left_tactics, hypothesis)?,
                    right_tactics: transform(&both.right_tactics, hypothesis)?,
                })),
                ProofTactic::Cases(proof_cases) => Ok(ProofTactic::Cases(
                    proof_cases.try_map_tactics(|tactics| transform(tactics, hypothesis))?,
                )),
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
            CType::Int8 => C0Type::Int8,
            CType::Int16 => C0Type::Int16,
            CType::Int32 => C0Type::Int32,
            CType::UInt8 => C0Type::UInt8,
            CType::UInt16 => C0Type::UInt16,
            CType::UInt32 => C0Type::UInt32,
            CType::Int64 => C0Type::Int64(LongRank::Long),
            CType::UInt64 => C0Type::UInt64(LongRank::Long),
            CType::Int128 => C0Type::Int128,
            CType::UInt128 => C0Type::UInt128,
            CType::Float32 => C0Type::Float32,
            CType::Float64 => C0Type::Float64,
            CType::Int8Pointer => C0Type::Int8Pointer,
            CType::Int16Pointer => C0Type::Int16Pointer,
            CType::UInt16Pointer => C0Type::UInt16Pointer,
            CType::Int32Pointer => C0Type::Int32Pointer,
            CType::UInt8Pointer => C0Type::UInt8Pointer,
            CType::UInt32Pointer => C0Type::UInt32Pointer,
            CType::Int64Pointer => C0Type::Int64Pointer(LongRank::Long),
            CType::Int128Pointer => C0Type::Int128Pointer,
            CType::UInt64Pointer => C0Type::UInt64Pointer(LongRank::Long),
            CType::UInt128Pointer => C0Type::UInt128Pointer,
            CType::Float32Pointer => C0Type::Float32Pointer,
            CType::Float64Pointer => C0Type::Float64Pointer,
            CType::Int8PointerPointer => C0Type::Int8PointerPointer,
            CType::Int16PointerPointer => C0Type::Int16PointerPointer,
            CType::UInt16PointerPointer => C0Type::UInt16PointerPointer,
            CType::Int32PointerPointer => C0Type::Int32PointerPointer,
            CType::UInt8PointerPointer => C0Type::UInt8PointerPointer,
            CType::UInt32PointerPointer => C0Type::UInt32PointerPointer,
            CType::Int64PointerPointer => C0Type::Int64PointerPointer(LongRank::Long),
            CType::Int128PointerPointer => C0Type::Int128PointerPointer,
            CType::UInt64PointerPointer => C0Type::UInt64PointerPointer(LongRank::Long),
            CType::UInt128PointerPointer => C0Type::UInt128PointerPointer,
            CType::Float32PointerPointer => C0Type::Float32PointerPointer,
            CType::Float64PointerPointer => C0Type::Float64PointerPointer,
            CType::FunctionPointer(signature) => C0Type::FunctionPointer(*signature),
            CType::Int8Array(length) => C0Type::Int8Array(*length),
            CType::Int16Array(length) => C0Type::Int16Array(*length),
            CType::UInt16Array(length) => C0Type::UInt16Array(*length),
            CType::Int32Array(length) => C0Type::Int32Array(*length),
            CType::UInt8Array(length) => C0Type::UInt8Array(*length),
            CType::UInt32Array(length) => C0Type::UInt32Array(*length),
            CType::PointerArray(element, length) => {
                C0Type::PointerArray(*element, LongRank::Long, *length)
            }
            CType::Int64Array(length) => C0Type::Int64Array(LongRank::Long, *length),
            CType::Int128Array(length) => C0Type::Int128Array(*length),
            CType::UInt64Array(length) => C0Type::UInt64Array(LongRank::Long, *length),
            CType::UInt128Array(length) => C0Type::UInt128Array(*length),
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
                ensuring: proof_if.ensuring.clone(),
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
            ProofTactic::Cases(proof_cases) => {
                Ok(ProofTactic::Cases(proof_cases.try_map_tactics(
                    |tactics| prepare_structural_induction_arm_tactics(tactics, setup, bindings),
                )?))
            }
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

fn check_pure_structural_induction(
    theorem: &TheoremDefinition,
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    tactics: &[ProofTactic],
) -> Result<
    (
        ProofCertificate,
        Vec<crate::kernel::proof::CheckedProposition>,
    ),
    ClickError,
> {
    let _timing = tactics
        .first()
        .and_then(|tactic| TacticTiming::pure_source(claim_label, vec![0], tactic));
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
        ContractEnvironment::new(&context.values, &context.array_refs),
        FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
        spec_definitions,
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
    // One normalization for every arm and every child hypothesis below, so a
    // `views` premise is the same premise in the same position in all of them.
    let theorem_requires = theorem_requirement_propositions(theorem)?;
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
                            | CType::Int8Array(_)
                            | CType::Int16Array(_)
                            | CType::UInt16Array(_)
                            | CType::Int32Array(_)
                            | CType::UInt8Array(_)
                            | CType::UInt32Array(_)
                            | CType::Int128Array(_)
                            | CType::Int64Array(_)
                            | CType::UInt128Array(_)
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
                        ContractEnvironment::new(
                            &branch_context.values,
                            &branch_context.array_refs,
                        ),
                        FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
                        spec_definitions,
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
            ContractEnvironment::new(&branch_context.values, &branch_context.array_refs),
            &branch_algebraic_values,
            &branch_context.memory,
            spec_definitions,
        )
        .map_err(ClickError::new)?;
        let mut branch_surface_requires = Vec::new();
        let mut branch_requires = Vec::new();
        for requirement in &theorem_requires {
            let surface = substitute_click_proposition(requirement, &case_substitution)
                .map_err(ClickError::new)?;
            let kernel = lower_pure_theorem_proposition_with_algebraic_values(
                claim_label,
                &surface,
                ContractEnvironment::new(&branch_context.values, &branch_context.array_refs),
                &branch_algebraic_values,
                &branch_context.memory,
                spec_definitions,
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
            for requirement in &theorem_requires {
                let surface = substitute_click_proposition(requirement, &child_substitution)
                    .map_err(ClickError::new)?;
                let kernel = lower_pure_theorem_proposition_with_algebraic_values(
                    claim_label,
                    &surface,
                    ContractEnvironment::new(&branch_context.values, &branch_context.array_refs),
                    &branch_algebraic_values,
                    &branch_context.memory,
                    spec_definitions,
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
                ContractEnvironment::new(&branch_context.values, &branch_context.array_refs),
                &branch_algebraic_values,
                &branch_context.memory,
                spec_definitions,
            )
            .map_err(ClickError::new)?;
            // As in `pure_induction_hypothesis`: the hypothesis is the
            // theorem's statement at the child, so a range premise carries the
            // byte-count guards of the range the child substitution moved it
            // to. `kernel_premises` keeps its positional pairing with
            // `surface_premises`, so the guards enter the implication only.
            let implication =
                kernel_premises
                    .iter()
                    .rev()
                    .fold(conclusion.clone(), |body, premise| {
                        let body = crate::kernel::stated_loadable_extent_guards(premise)
                            .into_iter()
                            .rev()
                            .fold(body, |body, guard| {
                                Proposition::Implies(Box::new(guard), Box::new(body))
                            });
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
        branch_context.surface_requirements = SurfacePropositionMap::default();
        for (surface, kernel) in branch_surface_requires.iter().zip(&branch_requires) {
            branch_context
                .surface_requirements
                .record_lowering(surface, kernel)?;
        }
        // The branch assumes this case's own requirements, so a range among
        // them carries its guards here too — the same list the branch's
        // hypothesis applications owe. Appended after the pairing above, which
        // a guard has no source clause for.
        for guard in branch_requires
            .iter()
            .flat_map(crate::kernel::stated_loadable_extent_guards)
            .collect::<Vec<_>>()
        {
            if !branch_requires.contains(&guard) {
                branch_requires.push(guard);
            }
        }
        branch_context.requires = branch_requires.clone();
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
            spec_definitions,
            theorem_environment,
            branch_setup,
        );
        let mut search = super::attempt::search_scope("pure structural induction arm");
        // The `induct` tactic is source tactic 0 and the arms follow it in
        // written order, each numbered through its own nested tactics.
        let first_source_index = 1 + arms[..arm_index]
            .iter()
            .map(|earlier| super::source_tactic_count(&earlier.tactics))
            .sum::<usize>();
        let sites = claim_script_sites(&root, &prepared, first_source_index);
        let attempted = match root.try_addressed_linear_script(&prepared, &sites, &mut None) {
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
        proof.record_accepted_trace(claim_label, completions.len());
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
    spec_definitions: SpecDefinitions<'_>,
) -> Result<PureTheoremContext, ClickError> {
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(theorem.parameters());
    let integer_values = pure_theorem_parameter_integer_values(theorem.parameters());
    let array_refs = pure_theorem_array_refs(theorem.parameters(), &values, &memory);
    // A theorem's premises are its `requires` clauses in source order, each
    // normalized to the proposition it states: a `views` range states its
    // readability, the same proposition `loadable` states. Keeping the list
    // positional is what keeps `requirement N` diagnostics and `apply … using`
    // lists naming the clause the reader wrote.
    let surface_requires = theorem_requirement_propositions(theorem)?;
    let mut requires = Vec::with_capacity(surface_requires.len());
    let mut requirement_assumptions = PureFactContext::new();
    for proposition in &surface_requires {
        let (lowered, _) = lower_pure_theorem_proposition_recording_introductions(
            theorem.name(),
            proposition,
            &requirement_assumptions,
            ContractEnvironment::new(&values, &array_refs),
            &BTreeMap::new(),
            &integer_values,
            &memory,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "theorem `{}` setup failed: could not lower requirement: {message}",
                theorem.name()
            ))
        })?;
        // Guard evidence is available to later requirements, while every
        // principal remains in the exported implication's premise list.
        requirement_assumptions = requirement_assumptions.assume_proposition(lowered.clone());
        requires.push(lowered);
    }
    let mut surface_requirements = SurfacePropositionMap::default();
    for (kernel, surface) in requires.iter().zip(&surface_requires) {
        surface_requirements.record_lowering(surface, kernel)?;
    }
    // A stated range premise carries its byte-count guards. Appending them
    // after the principal premises is the whole assume side for a theorem:
    // `context.requires` is what the theorem's own proof assumes and what the
    // exported implication demands of anyone who applies it, so one list makes
    // both directions agree. The zip above has already paired the principals
    // with their source clauses, and a guard has no source clause of its own.
    let mut requires = requires;
    // A narrow machine parameter's range is part of its typed domain. Keep
    // these guards in the exported premises as well as the proof context.
    for value in values.values() {
        for fact in crate::kernel::c_narrow_integer_range_facts(value).unwrap_or_default() {
            if !requires.contains(&fact) {
                requires.push(fact);
            }
        }
    }
    for guard in requires
        .iter()
        .flat_map(crate::kernel::stated_loadable_extent_guards)
        .collect::<Vec<_>>()
    {
        if !requires.contains(&guard) {
            requires.push(guard);
        }
    }
    let diagnostic_names = theorem
        .parameters()
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            let variable = match parameter.click_type() {
                ClickType::Algebraic(_) => {
                    crate::surface::lowering::algebraic_binder_variable(index).ok()?
                }
                ClickType::Integer => Variable(index as u64),
                _ => return None,
            };
            Some((variable, parameter.name().to_owned()))
        })
        .collect::<Vec<_>>()
        .into();
    Ok(PureTheoremContext {
        diagnostic_names,
        declaration_bindings: BTreeMap::new(),
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
    spec_definitions: SpecDefinitions<'_>,
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
        let context = pure_theorem_context(theorem, spec_definitions)?;
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
                ContractEnvironment::new(&context.values, &context.array_refs),
                &BTreeMap::new(),
                &context.integer_values,
                &context.memory,
                spec_definitions,
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
                C0Type::Int128 => CValue::Int128(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt128 => {
                    CValue::UInt128(Bitvector32Term::Variable(Variable(index as u64)))
                }
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
                C0Type::Int8 => CValue::Int8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int16 => CValue::Int16(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int32 => CValue::Int32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt32 => CValue::UInt32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Char(crate::languages::c::syntax::PlainChar::Unsigned) => {
                    CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::Char(crate::languages::c::syntax::PlainChar::Signed) => {
                    CValue::Int8(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::UInt8 => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt16 => CValue::UInt16(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int64(_) => {
                    CValue::Int64(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::UInt64(_) => {
                    CValue::UInt64(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::Float32 => {
                    CValue::Float32(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::Float64 => {
                    CValue::Float64(Bitvector32Term::Variable(Variable(index as u64)))
                }
                C0Type::Int8Pointer | C0Type::Int8Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            1,
                        ),
                    },
                    CType::Int8Pointer,
                ),
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
                C0Type::CharPointer(_)
                | C0Type::CharArray(_, _)
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
                C0Type::Int64Pointer(_) | C0Type::Int64Array(_, _) => CValue::typed_pointer(
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
                C0Type::Int128Pointer | C0Type::Int128Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            16,
                        ),
                    },
                    CType::Int128Pointer,
                ),
                C0Type::UInt64Pointer(_) | C0Type::UInt64Array(_, _) => CValue::typed_pointer(
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
                C0Type::UInt128Pointer | C0Type::UInt128Array(_) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            16,
                        ),
                    },
                    CType::UInt128Pointer,
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
                C0Type::Int8PointerPointer => {
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
                C0Type::Int32PointerPointer
                | C0Type::CharPointerPointer(_)
                | C0Type::UInt8PointerPointer
                | C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int128PointerPointer
                | C0Type::Int64PointerPointer(_)
                | C0Type::UInt128PointerPointer
                | C0Type::UInt64PointerPointer(_)
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
                C0Type::PointerArray(_, _, _) => CValue::typed_pointer(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            8,
                        ),
                    },
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

fn verify_theorem_ensure(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<VerifiedPureTheorem, ClickError> {
    // Resolve declaration aliases against the outer parameter values once.
    // Proof-local introductions can shadow either name without recapturing it.
    let scoped_context;
    let context = if ensure_clause.proof_bindings.is_empty() {
        context
    } else {
        scoped_context =
            context.with_declaration_bindings(&ensure_clause.proof_bindings, spec_definitions)?;
        &scoped_context
    };
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(
            crate::surface::validation::theorem_resource_conclusion_refusal(theorem.name()),
        ));
    };
    if let Some(verified) = verify_contract_refinement_theorem(
        theorem,
        ensure_index,
        ensure_clause,
        claim_label,
        surface_goal,
        context,
        spec_definitions,
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
        ContractEnvironment::new(&context.values, &context.array_refs),
        &BTreeMap::new(),
        &context.integer_values,
        &context.memory,
        spec_definitions,
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
                !matches!(ensure_clause.proof(), SourceProof::Default),
                matches!(
                    ensure_clause.proof(),
                    SourceProof::Tactic(SmartTactic::Auto)
                ),
                claim_label,
                context,
                surface_goal,
                &goal,
                &goal_introductions,
                spec_definitions,
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
                    spec_definitions,
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
                    spec_definitions,
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
            certificate_int32_rewrites(&certificate, claim_label, context, spec_definitions)
                .and_then(|rewrites| {
                    prove_universally_quantified_pure_implication_by_int32_rewrites(
                        context
                            .requires
                            .iter()
                            .map(crate::kernel::clone_proposition_iteratively)
                            .collect(),
                        goal.clone(),
                        variables.clone(),
                        rewrites,
                        completion,
                    )
                })
                .or_else(|| {
                    prove_universally_quantified_pure_implication(
                        context
                            .requires
                            .iter()
                            .map(crate::kernel::clone_proposition_iteratively)
                            .collect(),
                        goal.clone(),
                        variables,
                        completion,
                    )
                })
        }
        _ => None,
    };
    Ok(VerifiedPureTheorem {
        theorem_definition: clone_theorem_definition_iteratively(theorem),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind,
        proof: Some(certificate),
        requires: context
            .requires
            .iter()
            .map(crate::kernel::clone_proposition_iteratively)
            .collect(),
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
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<Option<VerifiedPureTheorem>, ClickError> {
    let ClickProposition::PredicateCall { name, arguments } = surface_goal else {
        return Ok(None);
    };
    let Some(contract_definition) = spec_definitions.predicates.contract_definition(name) else {
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
        let source_definition = spec_definitions
            .predicates
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
            c_function_contract_refinement_context(function_environment, name, spec_definitions.predicates.function_execution_name(target)).ok_or_else(
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
        ParameterBinding::new(&parameters, &arguments),
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
        ParameterBinding::new(&parameters, &arguments),
        obligations.entry(),
        obligations.post(),
        &snapshots,
        &surfaces,
        spec_definitions,
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
        ContractEnvironment::new(&context.values, &context.array_refs),
        &context.integer_values,
        &context.memory,
        spec_definitions,
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
/// The ordered int32 equalities a `rewrite ...; normalize` certificate cites.
///
/// Returns `None` for any other certificate shape, or when a cited surface
/// proposition does not lower.
fn certificate_int32_rewrites(
    certificate: &ProofCertificate,
    claim_label: &str,
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
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
                ContractEnvironment::new(&context.values, &context.array_refs),
                &context.memory,
                spec_definitions,
            )
            .ok(),
            _ => None,
        })
        .collect()
}

/// Addresses each tactic of a theorem's claim-level script by its source
/// tactic occurrence, in the flat pre-order numbering the source mapper,
/// `click expand` and `click profile` share, so a failure or a trace step
/// names the tactic the user wrote. `first` is the occurrence of
/// `tactics[0]`.
fn claim_script_sites(
    root: &Proof<'_>,
    tactics: &[ProofTactic],
    first: usize,
) -> Vec<ProofStepSite> {
    let mut next = first;
    tactics
        .iter()
        .map(|tactic| {
            let site = root.site().at_source_tactic(next);
            next += super::source_tactic_count(std::slice::from_ref(tactic));
            site
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn check_direct_pure_goal_with_proof(
    has_written_tactic: bool,
    // `by auto;` tries the solver before `simp`.
    auto: bool,
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &ClickProposition,
    goal: &Proposition,
    goal_introductions: &crate::kernel::LoweringIntroductions,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
) -> Result<(ProofCertificate, crate::kernel::proof::CheckedProposition), ClickError> {
    let root = Proof::for_pure_surface_goal(
        claim_label,
        &context.requires,
        goal.clone(),
        surface_goal.clone(),
        context,
        spec_definitions,
        theorem_environment,
    )
    .with_recorded_goal_introductions(Some(goal_introductions.clone()));
    let mut search = super::attempt::search_scope("pure theorem simp");
    // Default proof search has a budget and timing, but no written tactic
    // occurrence. Its failure belongs to the declaration, not a fabricated
    // `simp` site at the ensures clause.
    let (root, _timing) = if has_written_tactic {
        (
            root.at_source_tactic(0),
            TacticTiming::pure_source(claim_label, vec![0], &ProofTactic::Simp),
        )
    } else {
        (
            root,
            TacticTiming::new(claim_label, 0, 0, &ProofTactic::Simp, 0),
        )
    };
    let result = if auto {
        root.try_auto_proof_closure()
    } else {
        root.try_simp_closure()
    };
    let result = match result {
        Ok(result) => result,
        Err(error) => return Err(error.with_search_failures(search.finish())),
    };
    let Some(proof) = result else {
        return Err(root.simp_failure().with_search_failures(search.finish()));
    };
    search.succeed();
    // A traced theorem keeps its accepted path, as a traced function does.
    proof.record_accepted_trace(claim_label, 0);
    Ok((
        proof.completed_certificate()?,
        proof.completed_proposition()?,
    ))
}

/// Names whose declarations are checked directly against kernel arithmetic axioms.
fn integer_round_trip_destination(name: &str) -> Option<crate::kernel::MachineIntegerType> {
    use crate::kernel::MachineIntegerType;
    Some(match name {
        "integer_to_int8_round_trip" => MachineIntegerType::Int8,
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
        || crate::kernel::integer_truncation_law_requirements(name).is_some()
        || is_nat_integer_law_name(name)
        || matches!(
            name,
            "int32_add_defined_by_integer_bounds"
                | "int32_subtract_defined_by_integer_bounds"
                | "int64_add_defined_by_integer_bounds"
                | "int64_subtract_defined_by_integer_bounds"
                | "int64_to_integer_less_than_implies_less_than"
                | "int32_to_integer_equal_implies_equal"
                | "int32_add_to_integer"
                | "int32_remainder_to_integer"
                | "int32_to_integer_less_equal_implies_less_equal"
                | "int64_less_equal_to_integer"
                | "int64_less_than_to_integer"
                | "int64_greater_equal_to_integer"
                | "int64_to_integer_less_equal_implies_less_equal"
                | "int64_add_to_integer"
                | "int64_subtract_to_integer"
                | "int64_to_integer_equal_implies_equal"
                | "uint64_pack_uint16_to_integer"
                | "uint32_pack_uint16_to_integer"
                | "uint32_pack_uint16_high_first_to_integer"
                | "uint32_unpack_uint16_low"
                | "uint32_unpack_uint16_high"
                | "uint64_add_to_integer"
                | "uint64_multiply_to_integer"
                | "uint64_subtract_to_integer"
                | "uint64_divide_to_integer"
                | "uint64_remainder_to_integer"
                | "uint64_less_equal_to_integer"
                | "uint64_to_integer_less_equal_implies_less_equal"
                | "uint64_less_than_to_integer"
                | "uint64_to_integer_less_than_implies_less_than"
                | "uint64_less_than_implies_not_greater_equal"
                | "uint64_to_integer_equal_implies_equal"
                | "int32_less_equal_to_integer"
                | "int32_subtract_to_integer"
                | "int32_increment_upper_bound"
                | "int32_increment_strictly_increases"
                | "int32_increment_lower_bound"
                | "int32_increment_greater_equal_lower_bound"
                | "int32_increment_greater_than_lower_bound"
                | "int32_increment_preserves_order"
                | "int32_less_equal_less_than_transitive"
                | "int32_less_equal_transitive"
                | "int32_less_than_less_equal_transitive"
                | "int32_less_than_transitive"
                | "int32_greater_equal_transitive"
                | "int32_greater_equal_implies_reversed_less_equal"
                | "int32_less_equal_implies_reversed_greater_equal"
                | "int32_less_equal_and_not_less_than_implies_equal"
                | "int32_less_equal_and_not_equal_implies_less_than"
                | "int32_greater_equal_and_not_greater_than_implies_equal"
                | "int32_le_antisymmetric"
                | "int32_positive_is_nonnegative"
                | "int32_less_than_implies_less_equal"
                | "int32_less_than_implies_not_equal"
                | "int32_not_less_than_implies_greater_equal"
                | "int32_increment_below_max_is_defined"
                | "int32_increment_left_below_max_is_defined"
                | "int32_increment_left_strictly_increases"
                | "int32_nonnegative_add_within_max_is_defined"
                | "int32_nonnegative_subtract_within_value_is_defined"
                | "int32_move_one_from_right_to_left_preserves_sum"
                | "int32_add_nonnegative_right_is_at_least_left"
                | "int32_add_nonnegative_left_is_at_least_right"
                | "int32_above_one_predecessor_is_at_least_one"
                | "int32_positive_predecessor_is_nonnegative"
                | "int32_positive_predecessor_strictly_decreases"
                | "int32_nonnegative_predecessor_upper_bound"
                | "int32_increment_less_equal_implies_less_than"
                | "int32_less_than_increment_implies_less_equal"
                | "uint32_positive_predecessor_strictly_decreases"
                | "uint32_increment_upper_bound"
                | "uint32_increment_strictly_increases"
                | "uint32_widened_add_guard_by_integer_bound"
                | "uint32_add_to_integer"
                | "uint32_subtract_to_integer"
                | "uint32_multiply_to_integer"
                | "uint32_divide_to_integer"
                | "uint32_remainder_to_integer"
                | "uint32_multiply_guard_by_integer_bound"
                | "uint32_remainder_less_than_divisor"
                | "uint32_less_than_divisor_implies_remainder_is_value"
                | "uint32_less_equal_to_integer"
                | "uint32_to_integer_less_equal_implies_less_equal"
                | "uint32_to_integer_equal_implies_equal"
                | "uint32_less_than_implies_positive_difference"
                | "uint32_greater_than_implies_reversed_less_than"
                | "uint32_less_than_implies_reversed_greater_than"
                | "uint32_greater_equal_implies_reversed_less_equal"
                | "uint32_less_equal_implies_reversed_greater_equal"
                | "uint32_difference_decreases_after_increment"
                | "uint32_less_than_less_equal_transitive"
                | "uint32_less_equal_less_than_transitive"
                | "uint32_less_than_transitive"
                | "uint32_less_equal_transitive"
                | "uint64_less_than_less_equal_transitive"
                | "uint64_less_equal_and_not_less_than_implies_equal"
                | "uint64_less_equal_less_than_transitive"
                | "uint64_less_than_transitive"
                | "uint64_less_equal_transitive"
                | "int64_less_than_less_equal_transitive"
                | "int64_less_equal_less_than_transitive"
                | "int64_less_than_transitive"
                | "int64_less_equal_transitive"
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
        name if crate::kernel::integer_truncation_law_requirements(name).is_some() => (
            2,
            crate::kernel::integer_truncation_law_requirements(name).unwrap(),
        ),
        "int32_add_defined_by_integer_bounds"
        | "int32_subtract_defined_by_integer_bounds"
        | "int64_add_defined_by_integer_bounds"
        | "int64_subtract_defined_by_integer_bounds" => (2, 2),
        "int32_add_to_integer"
        | "int32_to_integer_less_equal_implies_less_equal"
        | "int64_less_equal_to_integer"
        | "int64_less_than_to_integer"
        | "int64_greater_equal_to_integer"
        | "int64_to_integer_less_equal_implies_less_equal"
        | "int64_to_integer_less_than_implies_less_than"
        | "int64_add_to_integer"
        | "int64_subtract_to_integer"
        | "int64_to_integer_equal_implies_equal"
        | "int32_less_equal_to_integer"
        | "int32_subtract_to_integer"
        | "int32_to_integer_equal_implies_equal"
        | "uint64_add_to_integer"
        | "uint64_multiply_to_integer"
        | "uint64_subtract_to_integer"
        | "uint64_less_equal_to_integer"
        | "uint64_to_integer_less_equal_implies_less_equal"
        | "uint64_less_than_to_integer"
        | "uint64_to_integer_less_than_implies_less_than"
        | "uint64_less_than_implies_not_greater_equal"
        | "uint64_to_integer_equal_implies_equal" => (2, 1),
        "uint64_pack_uint16_to_integer"
        | "uint32_pack_uint16_to_integer"
        | "uint32_pack_uint16_high_first_to_integer"
        | "uint32_unpack_uint16_low"
        | "uint32_unpack_uint16_high"
        | "uint64_divide_to_integer"
        | "uint64_remainder_to_integer"
        | "uint32_divide_to_integer"
        | "uint32_remainder_to_integer" => (2, 2),
        "int32_remainder_to_integer" => (2, 2),
        "int32_increment_upper_bound" | "int32_increment_strictly_increases" => (2, 1),
        "int32_increment_lower_bound"
        | "int32_increment_greater_equal_lower_bound"
        | "int32_increment_greater_than_lower_bound"
        | "int32_increment_preserves_order" => (3, 2),
        "int32_increment_less_equal_implies_less_than" => (2, 2),
        "int32_less_than_increment_implies_less_equal" => (2, 1),
        "int32_nonnegative_predecessor_upper_bound"
        | "int32_nonnegative_add_within_max_is_defined"
        | "int32_nonnegative_subtract_within_value_is_defined"
        | "int32_add_nonnegative_right_is_at_least_left"
        | "int32_add_nonnegative_left_is_at_least_right" => (2, 2),
        "int32_move_one_from_right_to_left_preserves_sum" => (3, 3),
        "int32_le_antisymmetric" => (2, 2),
        "int32_less_equal_and_not_less_than_implies_equal"
        | "int32_less_equal_and_not_equal_implies_less_than"
        | "int32_greater_equal_and_not_greater_than_implies_equal" => (2, 2),
        "int32_greater_equal_implies_reversed_less_equal" => (2, 1),
        "int32_less_equal_implies_reversed_greater_equal" => (2, 1),
        "int32_less_than_implies_less_equal"
        | "int32_less_than_implies_not_equal"
        | "int32_not_less_than_implies_greater_equal" => (2, 1),
        "int32_positive_is_nonnegative"
        | "int32_increment_below_max_is_defined"
        | "int32_increment_left_below_max_is_defined"
        | "int32_increment_left_strictly_increases"
        | "int32_above_one_predecessor_is_at_least_one"
        | "int32_positive_predecessor_is_nonnegative"
        | "int32_positive_predecessor_strictly_decreases" => (1, 1),
        "int32_less_equal_less_than_transitive"
        | "int32_less_equal_transitive"
        | "int32_less_than_less_equal_transitive"
        | "int32_less_than_transitive"
        | "int32_greater_equal_transitive" => (3, 2),
        "uint32_widened_add_guard_by_integer_bound"
        | "uint32_add_to_integer"
        | "uint32_subtract_to_integer"
        | "uint32_multiply_to_integer"
        | "uint32_multiply_guard_by_integer_bound"
        | "uint32_less_equal_to_integer"
        | "uint32_to_integer_less_equal_implies_less_equal"
        | "uint32_to_integer_equal_implies_equal"
        | "uint32_remainder_less_than_divisor"
        | "uint32_less_than_divisor_implies_remainder_is_value" => (2, 1),
        "uint32_positive_predecessor_strictly_decreases" => (1, 1),
        "uint32_increment_upper_bound"
        | "uint32_increment_strictly_increases"
        | "uint32_less_than_implies_positive_difference"
        | "uint32_greater_than_implies_reversed_less_than"
        | "uint32_less_than_implies_reversed_greater_than"
        | "uint32_greater_equal_implies_reversed_less_equal"
        | "uint32_less_equal_implies_reversed_greater_equal"
        | "uint32_difference_decreases_after_increment" => (2, 1),
        "uint32_less_than_less_equal_transitive"
        | "uint32_less_equal_less_than_transitive"
        | "uint32_less_than_transitive"
        | "uint32_less_equal_transitive" => (3, 2),
        name if crate::kernel::is_wide_order_transitivity_name(name) => (3, 2),
        "uint64_less_equal_and_not_less_than_implies_equal" => (2, 2),
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
    let axiom = if crate::kernel::integer_truncation_law_requirements(theorem.name()).is_some() {
        let parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.integer_values.get(parameter.name()) {
                Some(crate::kernel::SpecIntegerExpression::Term(value)) => Ok(value.clone()),
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be Integer",
                    parameter.name()
                ))),
            }
        };
        crate::kernel::prove_integer_truncation_law(theorem.name(), parameter(0)?, parameter(1)?)
            .expect("registered Integer truncation law")
    } else if is_nat_integer_law_name(theorem.name()) {
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
    } else if theorem.name().starts_with("uint64_") {
        let parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(CValue::UInt64(value)) => Ok(value.clone()),
                Some(CValue::PointerInteger(value))
                    if value.c_type() == crate::kernel::CType::UInt64 =>
                {
                    Ok(value.bits().clone())
                }
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be uint64",
                    parameter.name()
                ))),
            }
        };
        if crate::kernel::is_wide_order_transitivity_name(theorem.name()) {
            crate::kernel::prove_wide_order_transitive(
                theorem.name(),
                parameter(0)?,
                parameter(1)?,
                parameter(2)?,
            )
            .expect("registered uint64 transitivity")
        } else if theorem.name() == "uint64_less_equal_and_not_less_than_implies_equal" {
            crate::kernel::prove_uint64_le_and_not_lt_implies_eq(parameter(0)?, parameter(1)?)
        } else {
            crate::kernel::prove_uint64_integer_bridge(theorem.name(), parameter(0)?, parameter(1)?)
                .expect("registered uint64 observation bridge")
        }
    } else if theorem.name().starts_with("int64_") {
        let parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(CValue::Int64(value)) => Ok(value.clone()),
                Some(CValue::PointerInteger(value))
                    if value.c_type() == crate::kernel::CType::Int64 =>
                {
                    Ok(value.bits().clone())
                }
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be int64",
                    parameter.name()
                ))),
            }
        };
        let left = parameter(0)?;
        let right = parameter(1)?;
        match theorem.name() {
            name if crate::kernel::is_wide_order_transitivity_name(name) => {
                crate::kernel::prove_wide_order_transitive(name, left, right, parameter(2)?)
                    .expect("registered int64 transitivity")
            }
            "int64_add_defined_by_integer_bounds" => {
                crate::kernel::prove_int64_add_defined_by_integer_bounds(left, right)
            }
            "int64_subtract_defined_by_integer_bounds" => {
                crate::kernel::prove_int64_subtract_defined_by_integer_bounds(left, right)
            }
            "int64_to_integer_less_than_implies_less_than" => {
                crate::kernel::prove_int64_less_than_of_to_integer(left, right)
            }
            "int64_less_equal_to_integer" => {
                crate::kernel::prove_int64_less_equal_to_integer(left, right)
            }
            "int64_less_than_to_integer" => {
                crate::kernel::prove_int64_less_than_to_integer(left, right)
            }
            "int64_greater_equal_to_integer" => {
                crate::kernel::prove_int64_greater_equal_to_integer(left, right)
            }
            "int64_to_integer_less_equal_implies_less_equal" => {
                crate::kernel::prove_int64_less_equal_of_to_integer(left, right)
            }
            "int64_add_to_integer" => crate::kernel::prove_int64_add_to_integer(left, right),
            "int64_subtract_to_integer" => {
                crate::kernel::prove_int64_subtract_to_integer(left, right)
            }
            "int64_to_integer_equal_implies_equal" => {
                crate::kernel::prove_int64_equal_of_to_integer(left, right)
            }
            _ => unreachable!("only registered int64 bridges"),
        }
    } else if theorem.name().starts_with("uint32_") {
        let uint32_parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(CValue::UInt32(term)) => Ok(term.clone()),
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be uint32",
                    parameter.name()
                ))),
            }
        };
        let value = uint32_parameter(0)?;
        match theorem.name() {
            "uint32_unpack_uint16_low" => {
                crate::kernel::prove_uint32_unpack_uint16_low(value, uint32_parameter(1)?)
            }
            "uint32_unpack_uint16_high" => {
                crate::kernel::prove_uint32_unpack_uint16_high(value, uint32_parameter(1)?)
            }
            "uint32_pack_uint16_high_first_to_integer" => {
                crate::kernel::prove_unsigned_pack_u16_high_first_to_integer(
                    crate::kernel::MachineIntegerType::UInt32,
                    value,
                    uint32_parameter(1)?,
                )
                .expect("registered unsigned packing law")
            }
            "uint32_pack_uint16_to_integer" => crate::kernel::prove_unsigned_pack_u16_to_integer(
                crate::kernel::MachineIntegerType::UInt32,
                value,
                uint32_parameter(1)?,
            )
            .expect("registered unsigned packing law"),
            "uint32_widened_add_guard_by_integer_bound" => {
                crate::kernel::prove_uint32_widened_add_guard_by_integer_bound(
                    value,
                    uint32_parameter(1)?,
                )
            }
            "uint32_less_equal_to_integer" => {
                crate::kernel::prove_uint32_less_equal_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_to_integer_less_equal_implies_less_equal" => {
                crate::kernel::prove_uint32_less_equal_of_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_to_integer_equal_implies_equal" => {
                crate::kernel::prove_uint32_equal_of_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_remainder_less_than_divisor" => {
                crate::kernel::prove_uint32_remainder_less_than_divisor(value, uint32_parameter(1)?)
            }
            "uint32_less_than_divisor_implies_remainder_is_value" => {
                crate::kernel::prove_uint32_remainder_of_lt(value, uint32_parameter(1)?)
            }
            "uint32_add_to_integer" => {
                crate::kernel::prove_uint32_add_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_subtract_to_integer" => {
                crate::kernel::prove_uint32_subtract_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_divide_to_integer" => {
                crate::kernel::prove_uint32_divide_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_remainder_to_integer" => {
                crate::kernel::prove_uint32_remainder_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_multiply_to_integer" => {
                crate::kernel::prove_uint32_mul_to_integer(value, uint32_parameter(1)?)
            }
            "uint32_multiply_guard_by_integer_bound" => {
                crate::kernel::prove_uint32_mul_guard_by_integer_bound(value, uint32_parameter(1)?)
            }
            "uint32_positive_predecessor_strictly_decreases" => {
                prove_uint32_positive_predecessor_strictly_decreases(value)
            }
            "uint32_increment_upper_bound" => {
                prove_uint32_increment_upper_bound(value, uint32_parameter(1)?)
            }
            "uint32_increment_strictly_increases" => {
                prove_uint32_increment_strictly_increases(value, uint32_parameter(1)?)
            }
            "uint32_less_than_implies_positive_difference" => {
                prove_uint32_lt_implies_positive_difference(value, uint32_parameter(1)?)
            }
            "uint32_greater_than_implies_reversed_less_than" => {
                prove_uint32_gt_implies_reversed_lt(value, uint32_parameter(1)?)
            }
            "uint32_less_than_implies_reversed_greater_than" => {
                prove_uint32_lt_implies_reversed_gt(value, uint32_parameter(1)?)
            }
            "uint32_greater_equal_implies_reversed_less_equal" => {
                prove_uint32_ge_implies_reversed_le(value, uint32_parameter(1)?)
            }
            "uint32_less_equal_implies_reversed_greater_equal" => {
                prove_uint32_le_implies_reversed_ge(value, uint32_parameter(1)?)
            }
            "uint32_difference_decreases_after_increment" => {
                prove_uint32_difference_decreases_after_increment(value, uint32_parameter(1)?)
            }
            "uint32_less_than_less_equal_transitive" => {
                prove_uint32_lt_le_transitive(value, uint32_parameter(1)?, uint32_parameter(2)?)
            }
            "uint32_less_equal_less_than_transitive" => {
                prove_uint32_le_lt_transitive(value, uint32_parameter(1)?, uint32_parameter(2)?)
            }
            "uint32_less_than_transitive" => {
                prove_uint32_lt_transitive(value, uint32_parameter(1)?, uint32_parameter(2)?)
            }
            "uint32_less_equal_transitive" => {
                prove_uint32_le_transitive(value, uint32_parameter(1)?, uint32_parameter(2)?)
            }
            _ => unreachable!("checked above"),
        }
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
            "int32_subtract_defined_by_integer_bounds" => {
                crate::kernel::prove_int32_subtract_defined_by_integer_bounds(
                    value,
                    int32_parameter(1)?,
                )
            }
            "int32_add_to_integer" => {
                crate::kernel::prove_int32_add_to_integer(value, int32_parameter(1)?)
            }
            "int32_remainder_to_integer" => {
                crate::kernel::prove_int32_remainder_to_integer(value, int32_parameter(1)?)
            }
            "int32_to_integer_equal_implies_equal" => {
                crate::kernel::prove_int32_equal_of_to_integer(value, int32_parameter(1)?)
            }
            "int32_to_integer_less_equal_implies_less_equal" => {
                crate::kernel::prove_int32_less_equal_of_to_integer(value, int32_parameter(1)?)
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
            "int32_increment_greater_than_lower_bound" => {
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
            "int32_increment_less_equal_implies_less_than" => {
                prove_int32_successor_le_implies_lt(value, int32_parameter(1)?)
            }
            "int32_less_than_increment_implies_less_equal" => {
                prove_int32_lt_successor_implies_le(value, int32_parameter(1)?)
            }
            "int32_le_antisymmetric" => prove_int32_le_antisymmetric(value, int32_parameter(1)?),
            "int32_less_equal_and_not_less_than_implies_equal" => {
                prove_int32_le_and_not_lt_implies_eq(value, int32_parameter(1)?)
            }
            "int32_less_equal_and_not_equal_implies_less_than" => {
                prove_int32_le_and_neq_implies_lt(value, int32_parameter(1)?)
            }
            "int32_greater_equal_and_not_greater_than_implies_equal" => {
                prove_int32_ge_and_not_gt_implies_eq(value, int32_parameter(1)?)
            }
            "int32_positive_is_nonnegative" => prove_int32_positive_is_nonnegative(value),
            "int32_less_than_implies_less_equal" => {
                prove_int32_lt_implies_le(value, int32_parameter(1)?)
            }
            "int32_less_than_implies_not_equal" => {
                prove_int32_lt_implies_neq(value, int32_parameter(1)?)
            }
            "int32_not_less_than_implies_greater_equal" => {
                prove_int32_not_lt_implies_ge(value, int32_parameter(1)?)
            }
            "int32_increment_below_max_is_defined" => {
                prove_int32_increment_below_max_is_defined(value)
            }
            "int32_increment_left_below_max_is_defined" => {
                prove_int32_one_plus_below_max_is_defined(value)
            }
            "int32_increment_left_strictly_increases" => {
                prove_int32_one_plus_strictly_increases(value)
            }
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
            "int32_less_equal_less_than_transitive" => {
                prove_int32_le_lt_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_less_equal_transitive" => {
                prove_int32_le_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_less_than_less_equal_transitive" => {
                prove_int32_lt_le_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_less_than_transitive" => {
                prove_int32_lt_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_greater_equal_transitive" => {
                prove_int32_ge_transitive(value, int32_parameter(1)?, int32_parameter(2)?)
            }
            "int32_greater_equal_implies_reversed_less_equal" => {
                prove_int32_ge_implies_reversed_le(value, int32_parameter(1)?)
            }
            "int32_less_equal_implies_reversed_greater_equal" => {
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
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
) -> Result<(ProofCertificate, crate::kernel::proof::CheckedProposition), ClickError> {
    let root = match induction_setup {
        Some(setup) => Proof::for_pure_surface_goal_with_induction(
            claim_label,
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            context,
            spec_definitions,
            theorem_environment,
            setup.clone(),
        ),
        None => Proof::for_pure_surface_goal(
            claim_label,
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            context,
            spec_definitions,
            theorem_environment,
        ),
    }
    .with_recorded_goal_introductions(Some(goal_introductions.clone()));
    let mut search = super::attempt::search_scope("pure theorem script");
    let mut declined = None;
    let sites = claim_script_sites(&root, tactics, 0);
    let checked = match root.try_addressed_linear_script(tactics, &sites, &mut declined) {
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
    // A traced theorem keeps its accepted path, as a traced function does.
    proof.record_accepted_trace(claim_label, 0);
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
            ContractExpression::CUnary { operand: inner, .. }
            | ContractExpression::Negate(inner) => expression(inner, known_facts, applications),
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
            crate::surface::binary_contract_expression!(left, right) => {
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
            ClickProposition::ValidPlace {
                expression: value,
                range,
                ..
            } => {
                expression(value, known_facts, applications);
                if let Some((start, end)) = range {
                    expression(start, known_facts, applications);
                    expression(end, known_facts, applications);
                }
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
            | ClickProposition::Initialized { .. }
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
    contract_environment: ContractEnvironment<'_>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_opaque_calls(
        theorem_name,
        proposition,
        contract_environment,
        memory,
        spec_definitions,
        &BTreeSet::new(),
    )
}

pub(super) fn lower_pure_theorem_proposition_with_integer_values(
    theorem_name: &str,
    proposition: &ClickProposition,
    contract_environment: ContractEnvironment<'_>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_algebraic_and_integer_values(
        theorem_name,
        proposition,
        contract_environment,
        &BTreeMap::new(),
        integer_values,
        memory,
        spec_definitions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_with_algebraic_and_integer_values(
    theorem_name: &str,
    proposition: &ClickProposition,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_recording_introductions(
        theorem_name,
        proposition,
        &PureFactContext::new(),
        contract_environment,
        algebraic_values,
        integer_values,
        memory,
        spec_definitions,
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
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(Proposition, crate::kernel::LoweringIntroductions), String> {
    let state = CState::new().with_memory(memory.clone());
    lower_fixed_state_proposition_through_kernel_with_introductions(
        proposition,
        &PureFactContext::new(),
        contract_environment,
        FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
        spec_definitions,
        FixedStateLoweringOptions {
            algebraic_values: Some(algebraic_values),
            integer_values: Some(integer_values),
            obligation_assumptions: Some(assumptions),
            ..Default::default()
        },
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

pub(super) fn lower_pure_theorem_proposition_with_algebraic_values(
    theorem_name: &str,
    proposition: &ClickProposition,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_algebraic_and_integer_values(
        theorem_name,
        proposition,
        contract_environment,
        algebraic_values,
        &crate::persistent::PersistentMap::default(),
        memory,
        spec_definitions,
    )
}

/// A pure theorem's proposition lowered at its parameter state by the
/// kernel, with the calls named in `opaque_click_functions` kept as
/// applications.
fn lower_pure_theorem_proposition_with_opaque_calls(
    theorem_name: &str,
    proposition: &ClickProposition,
    contract_environment: ContractEnvironment<'_>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: &BTreeSet<String>,
) -> Result<Proposition, String> {
    let state = CState::new().with_memory(memory.clone());
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        &PureFactContext::new(),
        contract_environment,
        FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
        spec_definitions,
        FixedStateLoweringOptions {
            opaque_click_functions: Some(opaque_click_functions),
            ..Default::default()
        },
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

fn lower_pure_theorem_proposition_opaque(
    theorem_name: &str,
    proposition: &ClickProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    memory: &CMemory,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let opaque = spec_definitions
        .functions
        .definitions
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let state = CState::new().with_memory(memory.clone());
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        assumptions,
        contract_environment,
        FixedStateFrame::new(&state, &state, None, &RecordedSnapshots::new()),
        spec_definitions,
        FixedStateLoweringOptions {
            opaque_click_functions: Some(&opaque),
            ..Default::default()
        },
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pure_requirements_use_earlier_evaluation_guards_without_dropping_them() {
        for (parameters, arguments, expression, wrong_expression) in [
            ("n: int32", "n", "n + 1", "n - 1"),
            ("n: int64", "n", "n + 1i64", "n - 1i64"),
            ("n: uint32, d: uint32", "n, d", "n / d", "n * d"),
            ("n: uint64, d: uint64", "n, d", "n / d", "n * d"),
        ] {
            let guard = format!("requires defined({expression});");
            let observation = format!("requires to_integer({expression}) == 1;");
            let source = format!(
                "theorem guarded({parameters}) {{ {guard} {observation} ensures to_integer({expression}) == 1 by {{ assumption(); }} }}"
            );
            crate::surface::verify_c0_sources(&source, &[]).unwrap();
            let expanded =
                crate::surface::expand_c0_claim_source_by_label(&source, &[], "guarded.ensures_0")
                    .unwrap();
            crate::surface::verify_c0_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&guard, ""),
                source.replace(&guard, &format!("requires defined({wrong_expression});")),
                source.replace(
                    &format!("{guard} {observation}"),
                    &format!("{observation} {guard}"),
                ),
            ] {
                assert!(
                    crate::surface::verify_c0_sources(&invalid, &[]).is_err(),
                    "{invalid}"
                );
            }
            let caller = format!(
                "{source} theorem caller({parameters}) {{ {guard} {observation} ensures to_integer({expression}) == 1 by {{ apply(guarded({arguments})); assumption(); }} }}"
            );
            crate::surface::verify_c0_sources(&caller, &[]).unwrap();
        }
        let source = "theorem byte_at_next(bytes: uint8[], n: int32, value: Integer) { requires defined(n + 1); requires value == to_integer((int32)bytes[n + 1]); ensures value == to_integer((int32)bytes[n + 1]) by { assumption(); } }";
        crate::surface::verify_c0_sources(source, &[]).unwrap();
        assert!(
            crate::surface::verify_c0_sources(&source.replace("requires defined(n + 1);", ""), &[])
                .is_err()
        );
        let missing_call_guard = "theorem guarded(n: int32) { requires defined(n + 1); requires to_integer(n + 1) == 1; ensures n == n by { normalize(); } } theorem caller(n: int32) { ensures n == n by { apply(guarded(n)); normalize(); } }";
        assert!(crate::surface::verify_c0_sources(missing_call_guard, &[]).is_err());
    }

    #[test]
    fn ordinary_pure_scripts_retain_completion_without_compatibility() {
        for body in [
            "normalize();",
            "simp();",
            "have x == x by { simp(); } assumption();",
            "if x == 0 { normalize(); } else { normalize(); }",
        ] {
            let source = format!("theorem ordinary(x: int32) {{ ensures x == x by {{ {body} }} }}");
            let result = verify_instantiation_theorem(&source);
            let verified = result.unwrap();
            assert!(
                matches!(&verified.checked_completion, Some(TheoremProofCompletion::Proposition(completion)) if completion.proposition() == &verified.conclusion)
            );
            assert!(verified.kernel_authority.is_some());
            assert!(!verified.proof_certificate().unwrap().steps().is_empty());
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
    #[ignore = "nightly: 1.0s in the parallel gate"]
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
            let result = verify_instantiation_theorem(source);
            let verified = result.unwrap();
            assert!(matches!(
                verified.checked_completion,
                Some(TheoremProofCompletion::Proposition(_))
            ));
            assert!(verified.kernel_authority.is_some());
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
    fn numeric_induction_retains_partial_expression_requirements() {
        // A guarded addition in the conclusion must lower in the theorem's
        // requirement scope, including when building and applying its IH.
        let source = include_str!("../../../mdtests/pure_induction_guarded_offset.md")
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        crate::surface::verify_c0_sources(source, &[]).unwrap();
        let expanded =
            crate::surface::expand_c0_claim_source_by_label(source, &[], "guarded_count.ensures_0")
                .unwrap();
        crate::surface::verify_c0_sources(&expanded, &[]).unwrap();
        let missing_evidence = source.replace(
            "apply(ih(n - 1));",
            "apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }",
        );
        assert!(crate::surface::verify_c0_sources(&missing_evidence, &[]).is_err());
        let false_claim = source.replace(
            "ensures guarded_countdown(n) == 0 and",
            "ensures guarded_countdown(n) == 1 and",
        );
        assert!(crate::surface::verify_c0_sources(&false_claim, &[]).is_err());
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
            SpecDefinitions::new(&predicates, &functions),
            &TheoremEnvironment::new(&[]),
            None,
        )?;
        Ok(verified.remove(0))
    }

    #[test]
    fn pure_instantiate_retains_checked_authority_without_recertification() {
        let result = verify_instantiation_theorem(INSTANTIATE_BOUND);
        let verified = result.expect("pure instantiation must produce checked authority");
        assert!(verified.kernel_authority.is_some());
        assert!(matches!(
            verified.proof.as_ref().unwrap().steps(),
            [ProofStep::InstantiateUsing { .. }]
        ));
    }

    #[test]
    fn obtained_machine_witness_scope_retains_authority_and_expands() {
        let fixture = include_str!("../../../mdtests/obtain_pure_witness_scope.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let verified = verify_instantiation_theorem(source)
            .expect("obtained witnesses must resolve in later pure tactics");
        assert!(verified.kernel_authority.is_some());
        let expanded = crate::surface::expand_c0_claim_source_by_label(
            source,
            &[],
            "obtained_int32.ensures_0",
        )
        .unwrap();
        crate::surface::verify_c0_sources(&expanded, &[]).unwrap();
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
        // Named by its position and as written, not as a kernel term.
        assert!(
            error
                .message()
                .contains("premise 2 `x < limit` is not an available exact fact"),
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
        let verified = verify_instantiation_theorem(&source);
        assert!(verified.unwrap().kernel_authority.is_some());
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
            let spec_definitions = SpecDefinitions::new(&predicates, &functions);
            let theorems = TheoremEnvironment::new(&[]);
            let context = pure_theorem_context(theorem, spec_definitions).unwrap();
            let Ensure::Proposition(surface_goal) = theorem.ensures()[0].ensure() else {
                unreachable!()
            };
            let goal = lower_pure_theorem_proposition(
                theorem.name(),
                surface_goal,
                ContractEnvironment::new(&context.values, &context.array_refs),
                &context.memory,
                spec_definitions,
            )
            .unwrap();
            let root = Proof::for_pure_surface_goal(
                theorem.name(),
                &context.requires,
                goal.clone(),
                surface_goal.clone(),
                &context,
                spec_definitions,
                &theorems,
            );
            let certificate = ProofCertificate::from_proof_tactics(
                theorem.ensures()[0].proof().tactics().unwrap(),
            )
            .unwrap();
            let before = crate::persistent::persistent_node_allocations();
            let instantiated = root.apply_step(certificate.steps()[0].clone()).unwrap();
            allocations.push(crate::persistent::persistent_node_allocations() - before);
            // The instantiation adds the goal, which closes it.
            assert!(instantiated.is_complete());
            assert!(root.certificate().steps().is_empty());
            assert!(!root.facts().contains(&goal));
            instantiated.completed_proposition().unwrap();
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
                requires forall (k: int32) { k <= k };
                requires x == 0 or x != 0;
                ensures x <= x by {
                    if x == 0 {
                        instantiate(forall (k: int32) { k <= k }, x) using {}
                    } else {
                        instantiate(forall (k: int32) { k <= k }, x) using {}
                    }
                    assumption();
                }
            }
        "#;
        let cases = source
            .replace("if x == 0 {", "cases {\n x == 0 => {")
            .replace("} else {", "}\n x != 0 => {")
            .replace(
                "using {}\n                    }\n                    assumption();",
                "using {}\n                    }\n }\n                    assumption();",
            );
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
                assert!(matches!(arm.steps(), [ProofStep::InstantiateUsing { .. }]));
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
                "instantiate(forall (k: int32) { k <= k }, x) using {}",
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
            .with_contracts(file.contract_definitions(), &file.c_function_names);
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());
        let spec_definitions =
            SpecDefinitions::new(&predicate_environment, &click_function_environment);
        let theorem = file
            .theorem_definitions()
            .first()
            .ok_or_else(|| ClickError::new("test source did not contain a theorem"))?;
        let context = pure_theorem_context(theorem, spec_definitions)?;
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
            ContractEnvironment::new(&context.values, &context.array_refs),
            &BTreeMap::new(),
            &context.integer_values,
            &context.memory,
            spec_definitions,
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
    #[test]
    fn uint32_integer_order_bridges_check_exact_declarations() {
        for (name, premise, conclusion) in [
            (
                "uint32_less_equal_to_integer",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "uint32_to_integer_less_equal_implies_less_equal",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
        ] {
            let source = format!(
                "theorem {name}(left: uint32, right: uint32) {{ requires {premise}; ensures {conclusion}; }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace(&format!("requires {premise};"), ""),
                source.replace(
                    &format!("requires {premise};"),
                    &format!(
                        "requires {};",
                        premise
                            .replace("left", "TEMP")
                            .replace("right", "left")
                            .replace("TEMP", "right")
                    ),
                ),
                source.replace(conclusion, "true"),
                source.replace("left: uint32", "left: int32"),
                source.replace("right: uint32", "right: uint64"),
                source.replace("<=", "<"),
            ] {
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
        }
    }

    #[test]
    fn uint32_equality_bridge_checks_exact_declaration() {
        let source = "theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) { requires to_integer(left) == to_integer(right); ensures left == right; }";
        verify_standard_declaration(source).unwrap();
        for invalid in [
            source.replace("requires to_integer(left) == to_integer(right);", ""),
            source.replace(
                "requires to_integer(left) == to_integer(right);",
                "requires to_integer(left) <= to_integer(right);",
            ),
            source.replace("ensures left == right;", "ensures true;"),
            source.replace("ensures left == right;", "ensures left <= right;"),
            source.replace("left: uint32", "left: int32"),
            source.replace("right: uint32", "right: uint64"),
        ] {
            assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_subtract_bridge_checks_exact_declaration() {
        let source = "theorem uint32_subtract_to_integer(left: uint32, right: uint32) { requires right <= left; ensures to_integer(left - right) == to_integer(left) - to_integer(right); }";
        verify_standard_declaration(source).unwrap();
        for invalid in [
            source.replace("requires right <= left;", ""),
            source.replace("right <= left", "defined(left - right)"),
            source.replace("right <= left", "left <= right"),
            source.replace("left - right", "right - left"),
            source.replace("left: uint32", "left: int32"),
            source.replace("right: uint32", "right: uint64"),
            source.replace("to_integer(left) - to_integer(right);", "0;"),
        ] {
            assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_small_remainder_checks_exact_declaration() {
        let source = "theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) { requires value < divisor; ensures value % divisor == value; }";
        verify_standard_declaration(source).unwrap();
        for invalid in [
            source.replace("requires value < divisor;", ""),
            source.replace("value < divisor", "value <= divisor"),
            source.replace("value < divisor", "divisor != 0u32"),
            source.replace("value < divisor", "divisor < value"),
            source.replace("value % divisor", "divisor % value"),
            source.replace("== value", "== divisor"),
            source.replace("value: uint32", "value: int32"),
            source.replace("divisor: uint32", "divisor: uint64"),
        ] {
            assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_remainder_bound_checks_exact_declaration() {
        let source = "theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) { requires divisor != 0u32; ensures value % divisor < divisor; }";
        verify_standard_declaration(source).unwrap();
        for invalid in [
            source.replace("requires divisor != 0u32;", ""),
            source.replace("requires divisor != 0u32;", "requires value != 0u32;"),
            source.replace("< divisor;", "<= divisor;"),
            source.replace("value % divisor", "divisor % value"),
            source.replace("value: uint32", "value: int32"),
            source.replace("divisor: uint32", "divisor: uint64"),
        ] {
            assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_add_bridges_check_exact_kernel_declarations() {
        for (name, conclusion) in [
            (
                "uint32_widened_add_guard_by_integer_bound",
                "((int64)left + (int64)right) <= 4294967295i64",
            ),
            (
                "uint32_add_to_integer",
                "to_integer(left + right) == to_integer(left) + to_integer(right)",
            ),
        ] {
            let source = format!(
                "theorem {name}(left: uint32, right: uint32) {{ requires to_integer(left) + to_integer(right) <= 4294967295; ensures {conclusion}; }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace(
                    "requires to_integer(left) + to_integer(right) <= 4294967295;",
                    "",
                ),
                source.replace("<= 4294967295;", "<= 4294967296;"),
                source.replace("left: uint32", "left: int32"),
                source.replace("right: uint32", "right: uint64"),
                source.replace(conclusion, "true"),
            ] {
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
        }
    }
    #[test]
    fn wide_order_transitivity_declarations_reject_forged_premises_types_and_goals() {
        for ty in ["uint64", "int64"] {
            for (shape, first, second, conclusion) in [
                ("less_than_less_equal", "<", "<=", "<"),
                ("less_equal_less_than", "<=", "<", "<"),
                ("less_than", "<", "<", "<"),
                ("less_equal", "<=", "<=", "<="),
            ] {
                let declaration = |ty: &str, first: &str, second: &str, conclusion: &str| {
                    format!(
                        "theorem {ty_name}_{shape}_transitive(first: {ty}, middle: {ty}, last: {ty}) {{ requires first {first} middle; requires middle {second} last; ensures first {conclusion} last; }}",
                        ty_name = if ty == "uint32" { "uint64" } else { ty },
                    )
                };
                let source = declaration(ty, first, second, conclusion);
                verify_standard_declaration(&source)
                    .unwrap_or_else(|error| panic!("{source}: {}", error.message()));
                let weaker = |operator: &str| if operator == "<" { "<=" } else { "<" };
                let mut forged = vec![
                    // A premise the conclusion does not follow from.
                    source.replace("requires middle", "requires last"),
                    // The other kind's parameters under this kind's name.
                    source.replace(
                        &format!(": {ty}"),
                        if ty == "uint64" {
                            ": int64"
                        } else {
                            ": uint64"
                        },
                    ),
                    source.replace("ensures first", "ensures last"),
                ];
                if conclusion == "<=" {
                    forged.push(declaration(ty, first, second, "<"));
                } else {
                    // Weakening one strict premise changes which theorem
                    // this is; under this name it is refused.
                    if first == "<" {
                        forged.push(declaration(ty, weaker(first), second, conclusion));
                    }
                    if second == "<" {
                        forged.push(declaration(ty, first, weaker(second), conclusion));
                    }
                }
                for invalid in forged {
                    assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
                }
            }
        }
    }

    #[test]
    fn uint32_division_bridge_declarations_reject_forged_domains_types_and_goals() {
        for (name, op, mathematical) in [
            ("uint32_divide_to_integer", "/", "truncating_quotient"),
            ("uint32_remainder_to_integer", "%", "truncating_remainder"),
        ] {
            let source = format!(
                "theorem {name}(left: uint32, right: uint32) {{ requires right != 0u32; requires to_integer(right) != 0; ensures to_integer(left {op} right) == {mathematical}(to_integer(left), to_integer(right)); }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace("requires right != 0u32;", ""),
                source.replace("requires to_integer(right) != 0;", ""),
                source.replace("requires right != 0u32;", "requires left != 0u32;"),
                source.replace("requires right != 0u32;", "requires right == 0u32;"),
                source.replace("left: uint32", "left: uint64"),
                source.replace("right: uint32", "right: int32"),
                source.replace("right: uint32)", "right: uint32, extra: uint32)"),
                source.replace("));", ")) + 1;"),
            ] {
                assert_ne!(source, invalid);
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
        }
    }

    #[test]
    fn uint64_integer_bridge_declarations_reject_forged_guards_types_and_goals() {
        for (name, guard, goal) in [
            (
                "uint64_add_to_integer",
                "to_integer(left) + to_integer(right) <= 18446744073709551615",
                "to_integer(left + right) == to_integer(left) + to_integer(right)",
            ),
            (
                "uint64_multiply_to_integer",
                "to_integer(left) * to_integer(right) <= 18446744073709551615",
                "to_integer(left * right) == to_integer(left) * to_integer(right)",
            ),
            (
                "uint64_subtract_to_integer",
                "to_integer(right) <= to_integer(left)",
                "to_integer(left - right) == to_integer(left) - to_integer(right)",
            ),
            (
                "uint64_divide_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right))",
            ),
            (
                "uint64_remainder_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right))",
            ),
            (
                "uint64_less_equal_to_integer",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "uint64_to_integer_less_equal_implies_less_equal",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "uint64_less_than_to_integer",
                "left < right",
                "to_integer(left) < to_integer(right)",
            ),
            (
                "uint64_to_integer_less_than_implies_less_than",
                "to_integer(left) < to_integer(right)",
                "left < right",
            ),
            (
                "uint64_less_than_implies_not_greater_equal",
                "left < right",
                "not (left >= right)",
            ),
        ] {
            let source = format!(
                "theorem {name}(left: uint64, right: uint64) {{ requires {guard}; ensures {goal}; }}"
            );
            verify_standard_declaration(&source)
                .unwrap_or_else(|e| panic!("{name}: {}", e.message()));
            for invalid in [
                source.replace(&format!("requires {guard};"), ""),
                source.replace(
                    &format!("requires {guard};"),
                    "requires defined(left + right);",
                ),
                source
                    .replace("18446744073709551615", "18446744073709551616")
                    .replace(
                        "right != 0u64; requires to_integer(right) != 0",
                        "left != 0u64",
                    )
                    .replace("requires left <= right", "requires left >= right")
                    .replace("requires left < right", "requires left <= right")
                    .replace(
                        "requires to_integer(right) <= to_integer(left)",
                        "requires to_integer(left) <= to_integer(right)",
                    )
                    .replace(
                        "requires to_integer(left) <= to_integer(right)",
                        "requires to_integer(left) < to_integer(right)",
                    )
                    .replace("requires left < right", "requires left > right")
                    .replace(
                        "requires to_integer(left) < to_integer(right)",
                        "requires to_integer(right) < to_integer(left)",
                    ),
                source.replace("left: uint64", "left: int64"),
                source.replace("right: uint64", "right: uint32"),
                source.replace(&format!("ensures {goal};"), "ensures true;"),
                source.replace("; ensures", "; requires left == right; ensures"),
            ] {
                assert_ne!(source, invalid);
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
        }
    }

    #[test]
    fn unsigned_unpacking_declarations_require_exact_bounds_words_and_unsigned_shift() {
        for (name, extraction, result) in [
            ("low", "(((high << 16) | low) & 65535u32)", "low"),
            ("high", "((((high << 16) | low) >> 16) & 65535u32)", "high"),
        ] {
            let source = format!(
                "theorem uint32_unpack_uint16_{name}(low: uint32, high: uint32) {{ requires low <= 65535u32; requires high <= 65535u32; ensures {extraction} == {result}; }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace("requires low <= 65535u32;", ""),
                source.replace("requires high <= 65535u32;", ""),
                source.replace("65535", "65536"),
                source.replace("high << 16", "high << 15"),
                source.replace("& 65535u32", "& 32767u32"),
                source.replace(&format!("== {result};"), "== 0u32;"),
                source.replace(": uint32", ": int32"),
                source.replace(": uint32", ": uint64"),
            ] {
                assert_ne!(source, invalid);
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
            if name == "high" {
                assert!(verify_standard_declaration(&source.replace(">> 16", ">> 15")).is_err());
            }
        }
    }

    #[test]
    fn unsigned_packing_declarations_require_exact_fields_bounds_and_result() {
        for (ty, suffix, order) in [
            ("uint32", "u32", ""),
            ("uint32", "u32", "high_first_"),
            ("uint64", "u64", ""),
        ] {
            let packed = if order.is_empty() {
                "low | (high << 16)"
            } else {
                "(high << 16) | low"
            };
            let source = format!(
                "theorem {ty}_pack_uint16_{order}to_integer(low: {ty}, high: {ty}) {{ requires low <= 65535{suffix}; requires high <= 65535{suffix}; ensures to_integer({packed}) == to_integer(low) + 65536 * to_integer(high); }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace(&format!("requires low <= 65535{suffix};"), ""),
                source.replace(&format!("requires high <= 65535{suffix};"), ""),
                source.replace("65535", "65536"),
                source.replace("high << 16", "high << 15"),
                source.replace("65536 *", "65535 *"),
                source.replace(&format!("low: {ty}"), "low: int32"),
                source.replace("to_integer(low) + 65536", "to_integer(high) + 65536"),
            ] {
                assert_ne!(source, invalid);
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
        }
    }

    #[test]
    fn signed_integer_order_bridge_declarations_reject_wrong_guards_types_and_goals() {
        for (name, ty, premise, goal) in [
            (
                "int32_to_integer_less_equal_implies_less_equal",
                "int32",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "int64_less_equal_to_integer",
                "int64",
                "left <= right",
                "to_integer(left) <= to_integer(right)",
            ),
            (
                "int64_less_than_to_integer",
                "int64",
                "left < right",
                "to_integer(left) < to_integer(right)",
            ),
            (
                "int64_greater_equal_to_integer",
                "int64",
                "left >= right",
                "to_integer(left) >= to_integer(right)",
            ),
            (
                "int64_to_integer_less_equal_implies_less_equal",
                "int64",
                "to_integer(left) <= to_integer(right)",
                "left <= right",
            ),
            (
                "int64_to_integer_less_than_implies_less_than",
                "int64",
                "to_integer(left) < to_integer(right)",
                "left < right",
            ),
            (
                "int64_to_integer_equal_implies_equal",
                "int64",
                "to_integer(left) == to_integer(right)",
                "left == right",
            ),
        ] {
            let source = format!(
                "theorem {name}(left: {ty}, right: {ty}) {{ requires {premise}; ensures {goal}; }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace(&format!("requires {premise};"), ""),
                source.replace(&format!("requires {premise};"), "requires left > right;"),
                source.replace(&format!("ensures {goal};"), "ensures left > right;"),
                source.replace(&format!(": {ty}"), ": uint64"),
                source.replace(
                    &format!(": {ty}"),
                    if ty == "int64" { ": int32" } else { ": int64" },
                ),
                source.replace("; ensures", "; requires left == right; ensures"),
            ] {
                assert!(
                    verify_standard_declaration(&invalid).is_err(),
                    "forged declaration: {invalid}"
                );
            }
        }
    }
    #[test]
    fn int64_definedness_by_integer_bounds_declarations_reject_weaker_bounds_and_widths() {
        for (name, op, other) in [
            ("int64_add_defined_by_integer_bounds", "+", "-"),
            ("int64_subtract_defined_by_integer_bounds", "-", "+"),
        ] {
            let lower = format!("to_integer(left) {op} to_integer(right) >= -9223372036854775808");
            let upper = format!("to_integer(left) {op} to_integer(right) <= 9223372036854775807");
            let source = format!(
                "theorem {name}(left: int64, right: int64) {{ requires {lower}; requires {upper}; ensures defined(left {op} right); }}"
            );
            verify_standard_declaration(&source)
                .unwrap_or_else(|error| panic!("{name}: {}", error.message()));
            for invalid in [
                // Either bound alone does not exclude overflow.
                source.replace(&format!("requires {lower}; "), ""),
                source.replace(&format!("requires {upper}; "), ""),
                // A bound one past the range admits the overflowing value.
                source.replace("9223372036854775807", "9223372036854775808"),
                source.replace("-9223372036854775808", "-9223372036854775809"),
                // The other operation's bounds, and the other widths.
                source.replace(
                    &format!("to_integer(left) {op} to_integer(right)"),
                    &format!("to_integer(left) {other} to_integer(right)"),
                ),
                source.replace(": int64", ": int32"),
                source.replace(": int64", ": uint64"),
                source.replace(
                    &format!("defined(left {op} right)"),
                    &format!("defined(left {other} right)"),
                ),
            ] {
                assert_ne!(invalid, source);
                assert!(
                    verify_standard_declaration(&invalid).is_err(),
                    "forged declaration: {invalid}"
                );
            }
        }
    }
    #[test]
    fn int64_integer_operation_declarations_reject_wrong_guards_and_widths() {
        for (name, op, other) in [
            ("int64_add_to_integer", "+", "-"),
            ("int64_subtract_to_integer", "-", "+"),
        ] {
            let source = format!(
                "theorem {name}(left: int64, right: int64) {{ requires defined(left {op} right); ensures to_integer(left {op} right) == to_integer(left) {op} to_integer(right); }}"
            );
            verify_standard_declaration(&source).unwrap();
            for invalid in [
                source.replace(&format!("requires defined(left {op} right);"), ""),
                source.replace(
                    &format!("requires defined(left {op} right);"),
                    &format!("requires defined(left {other} right);"),
                ),
                source.replace(": int64", ": int32"),
                source.replace(": int64", ": uint64"),
                source.replace(" == ", " != "),
                source.replace("; ensures", "; requires left == right; ensures"),
            ] {
                assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
            }
        }
    }
    #[test]
    fn integer_truncation_declarations_reject_forged_guards_operands_and_types() {
        for (name, requirements, goal) in [
            (
                "integer_truncation_identity",
                &["d != 0"][..],
                "n == truncating_quotient(n, d) * d + truncating_remainder(n, d)",
            ),
            (
                "integer_positive_divisor_remainder_lower",
                &["d != 0", "0 < d"][..],
                "1 - d <= truncating_remainder(n, d)",
            ),
            (
                "integer_positive_divisor_remainder_upper",
                &["d != 0", "0 < d"][..],
                "truncating_remainder(n, d) <= d - 1",
            ),
            (
                "integer_nonnegative_dividend_remainder",
                &["d != 0", "0 <= n"][..],
                "0 <= truncating_remainder(n, d)",
            ),
            (
                "integer_nonpositive_dividend_remainder",
                &["d != 0", "n <= 0"][..],
                "truncating_remainder(n, d) <= 0",
            ),
        ] {
            let requires = requirements
                .iter()
                .map(|r| format!("requires {r}; "))
                .collect::<String>();
            let source =
                format!("theorem {name}(n: Integer, d: Integer) {{ {requires}ensures {goal}; }}");
            verify_standard_declaration(&source).unwrap();
            let mut invalid = vec![
                source.replace(": Integer", ": int32"),
                source.replace("truncating_remainder(n, d)", "truncating_remainder(d, n)"),
                source.replace(&format!("ensures {goal};"), "ensures n == d;"),
                source.replace("ensures", "requires n == d; ensures"),
                source.replace("ensures", "ensures n == n; ensures"),
            ];
            for guard in requirements {
                invalid.push(source.replace(&format!("requires {guard};"), ""));
                invalid.push(source.replace(
                    &format!("requires {guard};"),
                    &format!("requires not ({guard});"),
                ));
            }
            for forged in invalid {
                assert!(verify_standard_declaration(&forged).is_err(), "{forged}");
            }
        }
    }
}
