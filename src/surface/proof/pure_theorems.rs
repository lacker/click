use super::*;
use crate::kernel::AlgebraicValueType;
use crate::kernel::CompareRelation;
use crate::kernel::MachineIntegerType;
use crate::kernel::check_program_function_contract_refinement_obligations;

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
) -> Result<Vec<SyntaxProposition>, ClickError> {
    theorem
        .requires()
        .iter()
        .map(|requirement| {
            requirement.theorem_proposition().ok_or_else(|| {
                ClickError::new(crate::surface::validation::theorem_resource_clause_refusal(
                    theorem.name(),
                ))
                .with_proof_refusal(ProofRefusal::Contract)
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
    function_environment: Option<&ExecutionEnvironment>,
    resource_environment: &ResourceEnvironment,
    function_source_registry: Arc<FunctionSourceRegistry>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = dependencies;
    for theorem in theorem_definitions {
        if theorem.is_interface_export() {
            theorem_environment.insert(clone_theorem_definition_iteratively(theorem));
            continue;
        }
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
/// type; that is the form [`verify_concrete_theorem_definition`] takes. A
/// kernel law over an index type is the exception: a C index has no rigid
/// type, so the law is checked at each index type its kernel rule admits
/// ([`kernel_law_index_types`]).
pub(in crate::surface) fn verify_theorem_definition(
    theorem: &TheoremDefinition,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&ExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    if theorem.type_parameters().is_empty() {
        return verify_concrete_theorem_definition(
            theorem,
            spec_definitions,
            theorem_environment,
            function_environment,
        );
    }
    let pointer_elements = theorem
        .parameters()
        .iter()
        .filter_map(|parameter| match parameter.click_type() {
            ClickType::Program(InterfaceType::ParameterPointer(element)) => Some(element.name()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    let substitution = theorem
        .type_parameters()
        .iter()
        .map(|name| {
            (
                name.clone(),
                generics::TypeArgument::from(if pointer_elements.contains(name.as_str()) {
                    ClickType::Program(InterfaceType::Parameter(
                        crate::kernel::TypeParameterName::intern(name),
                    ))
                } else {
                    ClickType::Algebraic(AlgebraicTypeApplication {
                        rigid: true,
                        name: name.clone(),
                        arguments: Vec::new(),
                    })
                }),
            )
        })
        .collect();
    let instantiate = |substitution: &generics::TypeSubstitution| {
        let mut symbolic =
            generics::instantiate_theorem(theorem, substitution).map_err(ClickError::new)?;
        symbolic.name = theorem.name().to_string();
        verify_concrete_theorem_definition(
            &symbolic,
            spec_definitions,
            theorem_environment,
            function_environment,
        )
    };
    let Some((index_parameter, index_types)) = kernel_law_index_types(theorem.name()) else {
        return instantiate(&substitution);
    };
    let mut verified = Vec::new();
    for index_type in index_types {
        let mut instance = substitution.clone();
        instance.insert(
            index_parameter.to_string(),
            generics::TypeArgument::from(ClickType::Program(index_type)),
        );
        verified.extend(instantiate(&instance)?);
    }
    Ok(verified)
}

/// The index parameter and concrete formats admitted by a trusted descriptor law.
pub(in crate::surface) fn kernel_law_index_types(
    name: &str,
) -> Option<(&'static str, Vec<InterfaceType>)> {
    let formats = match name {
        "click::separation::separate_elements" | "click::separation::distinct_elements" => vec![
            InterfaceType::Int32,
            InterfaceType::Int64(crate::languages::c::syntax::LongRank::Long),
            InterfaceType::UInt64(crate::languages::c::syntax::LongRank::Long),
        ],
        "click::separation::contains_subrange"
        | "click::separation::contains_element"
        | "click::separation::contains_rebase"
        | "click::separation::contains_joined_ranges"
        | "click::separation::separate_adjacent_ranges" => vec![
            InterfaceType::Int32,
            InterfaceType::UInt64(crate::languages::c::syntax::LongRank::Long),
        ],
        _ => return None,
    };
    Some(("I", formats))
}

pub(in crate::surface) fn verify_concrete_theorem_definition(
    theorem: &TheoremDefinition,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&ExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    #[cfg(test)]
    crate::kernel::search::record_discovery("verify_concrete_theorem_definition");
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
    pub(super) declaration_bindings: BTreeMap<String, SyntaxTerm>,
    /// The theorem's starting point: the memory it quantifies over, as the
    /// first point of a path of its own.
    pub(super) point: crate::kernel::ProgramPoint,
    pub(super) values: ProgramValueBindings,
    pub(super) integer_values: PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    pub(super) array_refs: ClickArrayRefs,
    pub(super) requires: Vec<Proposition>,
    pub(super) surface_requirements: SurfacePropositionMap,
}

impl PureTheoremContext {
    fn with_declaration_bindings(
        &self,
        bindings: &[(String, Option<ClickType>, SyntaxTerm)],
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
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(value.clone())),
                );
            } else if let Some(value) = self.integer_values.get(&name) {
                let captured = SurfaceBinder::fresh();
                substitutions.insert(name, captured.reference());
                context.integer_values = context
                    .integer_values
                    .with_inserted(captured, value.clone());
            }
        }
        let assumptions = assumptions_from_propositions(&context.requires);
        for (name, click_type, value) in bindings {
            let value =
                substitute_contract_expression(value, &substitutions).map_err(ClickError::new)?;
            let promoted = super::surface_lowering::promote_integer_expression(
                &value,
                &context.integer_values,
                &PersistentBinderMap::default(),
            );
            let referenced_binders = || {
                let mut binders = BinderSet::new();
                collect_contract_expression_referenced_binders(&promoted, &mut binders);
                binders
            };
            let is_integer = match click_type.as_ref() {
                Some(ClickType::Integer) => true,
                Some(_) => false,
                None if matches!(value, SyntaxTerm::Lambda { .. })
                    || lambdas::is_proposition_value(&value)
                    || matches!(&value, SyntaxTerm::Call { name, .. } if spec_definitions.functions.get(name).is_some_and(|definition| definition.return_type() == &ClickType::Proposition)) =>
                {
                    false
                }
                None => referenced_binders()
                    .into_iter()
                    .any(|binder| context.integer_values.get(&binder).is_some()),
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
                        let state = ExecutionState::at_point(&context.point);
                        let integer_values = referenced_binders()
                            .into_iter()
                            .filter_map(|name| {
                                context
                                    .integer_values
                                    .get(&name)
                                    .map(|value| (name, value.clone()))
                            })
                            .fold(PersistentBinderMap::default(), |values, (name, value)| {
                                values.with_inserted(name, value)
                            });
                        let spec = crate::surface::lowering::elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
                            &SyntaxProposition::Comparison {
                                left: promoted,
                                operator: ComparisonOperator::Equal,
                                right: SyntaxTerm::IntegerLiteral("0".into()),
                            }, BTreeMap::new(), BTreeMap::new(), &state, &state, ProgramValueBindings::new(), ProgramValueBindings::new(),
                            BTreeMap::new(), &integer_values, None, &RecordedStates::new(), spec_definitions,
                            BTreeSet::new(), BTreeMap::new(), None,).map_err(ClickError::new)?;
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
                let captured = SurfaceBinder::fresh();
                let reference = captured.reference();
                context.integer_values = context.integer_values.with_inserted(captured, value);
                reference
            } else if crate::surface::lowering::narrow_typed_arithmetic(click_type.as_ref(), &value)
            {
                // A narrow typed `let` names its native sum (G2), as the
                // clauses read it; the bare value would be C's promoted one.
                SyntaxTerm::Let {
                    name: name.clone().into(),
                    click_type: click_type.clone(),
                    value: Box::new(value),
                    body: Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                        (name.clone()).into(),
                    ))),
                }
            } else {
                value
            };
            substitutions.insert(name.clone(), value.clone());
            context.declaration_bindings.insert(name.clone(), value);
        }
        Ok(context)
    }
}

/// The checked theorem statement and descent rule for this proof's local
/// induction hypothesis. Surface calls have already resolved to that binding.
#[derive(Clone, Debug)]
pub(super) struct PureInductionSetup {
    pub(super) parameter: String,
    pub(super) hypothesis: String,
    pub(super) surface_requires: Vec<SyntaxProposition>,
    pub(super) surface_goal: SyntaxProposition,
    /// Present for algebraic induction; applications may instantiate all parameters.
    pub(super) structural_parameters: Option<Vec<FunctionParameter>>,
    pub(super) structural_root: Option<crate::kernel::AlgebraicTerm>,
}

#[derive(Clone, Debug)]
pub(super) struct PureStructuralInductionApplication {
    /// The selected theorem's exact requirements and their written forms.
    pub(super) kernel_premises: Vec<Proposition>,
    pub(super) surface_premises: Vec<SyntaxProposition>,
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
    pub(super) algebraic_values: BTreeMap<String, SpecAlgebraicExpression>,
}

/// The bare parameter or binding name an induction argument spells, when it
/// spells one rather than a compound term.
pub(super) fn induction_argument_name(argument: &SyntaxTerm) -> Option<&str> {
    match argument {
        SyntaxTerm::Binding(name)
        | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => Some(name),
        SyntaxTerm::AlgebraicVariable { name, .. } => name.written(),
        _ => None,
    }
}

/// The argument occupying the inducted position of one hypothesis
/// application. This is the only position that must descend; a one-argument
/// application spells that position alone.
pub(super) fn structural_induction_descent_argument(
    parameter_index: usize,
    arguments: &[SyntaxTerm],
) -> Option<&SyntaxTerm> {
    if arguments.len() == 1 {
        arguments.first()
    } else {
        arguments.get(parameter_index)
    }
}

/// The substitution one `ih(...)` application makes in the theorem's own
/// clauses.
///
/// A proof may spell every parameter in declaration order, which is how the
/// hypothesis is instantiated at parameters other than the inducted one, or
/// spell the inducted position alone, which leaves every other parameter at
/// its current value. A position that names its own parameter substitutes
/// nothing, so the theorem's own elaboration of that parameter is retained.
pub(super) fn structural_induction_hypothesis_substitution(
    parameters: &[FunctionParameter],
    parameter: &str,
    hypothesis: &str,
    arguments: &[SyntaxTerm],
) -> Result<BTreeMap<String, SyntaxTerm>, ClickError> {
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

pub(super) fn pure_induction_hypothesis(
    setup: &PureInductionSetup,
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, ClickError> {
    let (current_variable, unsigned) = match context.values.get(&setup.parameter) {
        Some(ProgramValue::Int32(OldMachineTerm::Variable(variable))) => (variable, false),
        Some(ProgramValue::UInt64(OldMachineTerm::Variable(variable))) => (variable, true),
        _ => return Err(ClickError::new("invalid scalar induction parameter")),
    };
    // Lower the hypothesis in its own requirement scope. These premises
    // are retained below as implications, so definedness is never granted
    // to an application that does not establish the smaller argument's guards.
    // Mathematical parameters keep the same Integer bindings as the theorem.
    let mut assumptions = PureFactContext::new();
    let mut opaque_requirements = Vec::new();
    for requirement in &setup.surface_requires {
        let lowered = lower_pure_theorem_proposition_opaque(
            &setup.hypothesis,
            requirement,
            &assumptions,
            context,
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
        context,
        spec_definitions,
    )
    .map_err(ClickError::new)?;
    let mut propositions = opaque_requirements.clone();
    propositions.push(opaque_goal.clone());
    // The decrease guard names the measure beside the binder, so the binder
    // avoids it even when neither the goal nor a requirement mentions it.
    let variable = fresh_int32_variable_for_propositions(&propositions, &[*current_variable]);
    let value = OldMachineTerm::Variable(variable);
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
        // the conclusion at an argument where the range's span wraps, which
        // is an argument the theorem itself never covered.
        for guard in crate::kernel::stated_loadable_span_guards(&requirement)
            .into_iter()
            .rev()
        {
            body = Proposition::Implies(Box::new(guard), Box::new(body));
        }
        body = Proposition::Implies(Box::new(requirement), Box::new(body));
    }
    let smaller = Proposition::condition_is(
        if unsigned {
            OldConditionTerm::uint64_less_than(
                value.clone(),
                OldMachineTerm::Variable(*current_variable),
            )
        } else {
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(value.clone()),
                right: Box::new(OldMachineTerm::Variable(*current_variable)),
            }
        },
        true,
    );
    body = Proposition::Implies(Box::new(smaller), Box::new(body));
    if !unsigned {
        let nonnegative = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(value),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        );
        body = Proposition::Implies(Box::new(nonnegative), Box::new(body));
    }
    crate::kernel::quantifiers::close_forall(
        Default::default(),
        variable,
        if unsigned {
            Sort::ProgramInteger(MachineIntegerType::UInt64)
        } else {
            Sort::ProgramInt32
        },
        &body,
    )
    .ok_or_else(|| ClickError::new("the induction hypothesis's quantifier does not close"))
}

fn prepare_pure_induction_setup(
    theorem: &TheoremDefinition,
    goal: &SyntaxProposition,
    tactics: &[ProofTactic],
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Option<PureInductionSetup>, ClickError> {
    fn declarations<'a>(tactics: &'a [ProofTactic], found: &mut Vec<(&'a String, &'a String)>) {
        for tactic in tactics {
            if let ProofTactic::Induct {
                parameter,
                hypothesis,
            } = tactic
            {
                found.push((parameter, hypothesis));
            }
            for child in tactic.children() {
                let (TacticChild::Continuing(proof) | TacticChild::Obligation(proof)) = child;
                if let Some(body) = proof.tactics() {
                    declarations(body, found);
                }
            }
        }
    }

    let mut found = Vec::new();
    declarations(tactics, &mut found);
    let Some(&(parameter, hypothesis)) = found.first() else {
        return Ok(None);
    };
    let structural = theorem
        .parameters()
        .iter()
        .any(|p| p.name() == parameter && matches!(p.click_type(), ClickType::Algebraic(_)));
    if structural
        && found
            .iter()
            .any(|&(p, h)| p != parameter || h != hypothesis)
    {
        return Err(ClickError::new(
            "structural induction declarations must name the same theorem parameter and hypothesis",
        )
        .with_proof_refusal(ProofRefusal::Tactic)
        .with_failed_tactic("induct"));
    }
    if !theorem.parameters().iter().any(|candidate| {
        candidate.name() == parameter
            && matches!(
                candidate.click_type(),
                ClickType::Algebraic(_)
                    | ClickType::Program(InterfaceType::Int32 | InterfaceType::UInt64(_))
            )
    }) {
        return Err(ClickError::new(format!(
            "`induct({parameter})` requires an int32 or uint64 theorem parameter with that name"
        ))
        .with_proof_refusal(ProofRefusal::Tactic)
        .with_failed_tactic("induct"));
    }
    let surface_requires = theorem_requirement_propositions(theorem)?;

    if !structural
        && (found.len() != 1
            || !tactics
                .iter()
                .any(|tactic| matches!(tactic, ProofTactic::Induct { .. })))
    {
        return Err(ClickError::new(
            "a pure theorem proof may contain only one top-level `induct` tactic",
        ));
    }
    let structural_root = if structural {
        let (index, p) = theorem
            .parameters()
            .iter()
            .enumerate()
            .find(|(_, p)| p.name() == parameter)
            .expect("checked induction parameter");
        let ClickType::Algebraic(algebraic_type) = p.click_type() else {
            unreachable!()
        };
        let state = ExecutionState::at_point(&context.point);
        let captured = capture_fixed_state_algebraic_expression(
            &SyntaxTerm::AlgebraicVariable {
                name: parameter.clone().into(),
                algebraic_type: algebraic_type.clone(),
                binder_index: index,
            },
            ContractEnvironment::new(&context.values, &context.array_refs),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            spec_definitions,
        )
        .map_err(ClickError::new)?;
        let crate::kernel::SpecAlgebraicExpressionNode::Variable(variable) = captured.node else {
            return Err(ClickError::new(
                "structural induction requires a symbolic theorem parameter",
            ));
        };
        Some(crate::kernel::AlgebraicTerm {
            algebraic_type: captured.algebraic_type,
            node: crate::kernel::AlgebraicTermNode::Variable(variable),
        })
    } else {
        None
    };
    Ok(Some(PureInductionSetup {
        parameter: parameter.clone(),
        hypothesis: hypothesis.clone(),
        surface_requires,
        surface_goal: goal.clone(),
        structural_root,
        structural_parameters: structural.then(|| theorem.parameters().to_vec()),
    }))
}

pub(super) fn click_type_from_algebraic_value_type(
    value_type: &AlgebraicValueType,
) -> Result<ClickType, ClickError> {
    Ok(generics::click_type_from_algebraic_value_type(value_type))
}

pub(super) fn pure_theorem_context(
    theorem: &TheoremDefinition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<PureTheoremContext, ClickError> {
    let memory = SymbolicMemory::new();
    // The theorem is stated over one memory: its requirements and its proof
    // all stand at the point that starts there.
    let point = crate::kernel::ProgramPoint::starting_at(&memory);
    let values = pure_theorem_parameter_values_with_generic_pointers(
        theorem.parameters(),
        &theorem.generic_pointer_parameters,
    );
    let integer_values = pure_theorem_parameter_integer_values(theorem.parameters());
    let array_refs = pure_theorem_array_refs(theorem.parameters(), &values, &point);
    // A theorem's premises are its `requires` clauses in source order, each
    // normalized to the proposition it states: a `views` range states its
    // readability, the same proposition `loadable` states. Keeping the list
    // positional is what keeps `requirement N` diagnostics and `apply … using`
    // lists naming the clause the reader wrote.
    let surface_requires = theorem_requirement_propositions(theorem)?;
    let mut requires = Vec::with_capacity(surface_requires.len());
    let mut requirement_assumptions = PureFactContext::new();
    for proposition in &surface_requires {
        let state = ExecutionState::at_point(&point);
        let (lowered, _, _) = lower_stated_proposition(
            proposition,
            &PureFactContext::new(),
            ContractEnvironment::new(&values, &array_refs),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            spec_definitions,
            FixedStateLoweringOptions {
                integer_values: Some(&integer_values),
                obligation_assumptions: Some(&requirement_assumptions),
                ..Default::default()
            },
        )
        .map_err(|reason| {
            let diagnostic = ClickError::new(format!(
                "theorem `{}` setup failed: could not lower requirement: pure theorem `{}`: {reason}",
                theorem.name(),
                theorem.name(),
            )).at_declaration(theorem.name());
            theorem_statement_error(diagnostic, reason)
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
    for guard in requires
        .iter()
        .flat_map(crate::kernel::stated_loadable_span_guards)
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
                ClickType::Integer
                | ClickType::Resource
                | ClickType::Program(InterfaceType::Float32 | InterfaceType::Float64) => {
                    Variable(index as u64)
                }
                _ => return None,
            };
            Some((variable, parameter.name().to_owned()))
        })
        .collect::<Vec<_>>()
        .into();
    Ok(PureTheoremContext {
        diagnostic_names,
        // Synthesized obligations use names too. Retain the declared model
        // parameters' types and identities for those generated expressions.
        declaration_bindings: theorem
            .parameters()
            .iter()
            .enumerate()
            .filter_map(|(binder_index, parameter)| {
                let ClickType::Algebraic(algebraic_type) = parameter.click_type() else {
                    return None;
                };
                let name = parameter.name().to_owned();
                Some((
                    name.clone(),
                    SyntaxTerm::AlgebraicVariable {
                        name: name.into(),
                        algebraic_type: algebraic_type.clone(),
                        binder_index,
                    },
                ))
            })
            .collect(),
        point,
        values,
        integer_values,
        array_refs,
        requires,
        surface_requirements,
    })
}

fn theorem_statement_error(
    diagnostic: ClickError,
    refusal: StatedPropositionRefusal,
) -> ClickError {
    use crate::kernel::ExecutionLimit;
    match refusal {
        StatedPropositionRefusal::Elaboration(_) | StatedPropositionRefusal::Evaluation(_) => {
            diagnostic.with_proof_refusal(ProofRefusal::Contract)
        }
        StatedPropositionRefusal::Stopped(
            ExecutionLimit::GuardedConjunctionTooLong
            | ExecutionLimit::SymbolicPointerConditional
            | ExecutionLimit::UnsupportedPureFunctionResult(_),
            _,
        ) => diagnostic.with_kind(ClickErrorKind::Unsupported),
        StatedPropositionRefusal::Stopped(
            ExecutionLimit::BoolArithmetic
            | ExecutionLimit::BoolComparedWithInteger
            | ExecutionLimit::BoolOrdered
            | ExecutionLimit::MixedBoolArms,
            _,
        ) => diagnostic.with_proof_refusal(ProofRefusal::Contract),
        StatedPropositionRefusal::Stopped(..) | StatedPropositionRefusal::Lowering(_) => {
            diagnostic.with_kind(ClickErrorKind::Internal)
        }
    }
}

fn pure_theorem_parameter_integer_values(
    parameters: &[FunctionParameter],
) -> PersistentBinderMap<crate::kernel::SpecIntegerExpression> {
    parameters
        .iter()
        .enumerate()
        .filter(|(_, parameter)| matches!(parameter.click_type(), ClickType::Integer))
        .fold(
            PersistentBinderMap::default(),
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
) -> ProgramValueBindings {
    pure_theorem_parameter_values_with_generic_pointers(parameters, &BTreeSet::new())
}

fn pure_theorem_parameter_values_with_generic_pointers(
    parameters: &[FunctionParameter],
    generic_pointers: &BTreeSet<String>,
) -> ProgramValueBindings {
    parameters
        .iter()
        .enumerate()
        .filter_map(|(index, parameter)| {
            let interface_type = parameter.click_type().interface_type()?;
            let value = match interface_type {
                InterfaceType::Int128 => {
                    ProgramValue::Int128(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::UInt128 => {
                    ProgramValue::UInt128(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Parameter(name) => crate::kernel::symbolic_call_result(
                    ProgramType::Parameter(name),
                    Variable(index as u64),
                ),
                InterfaceType::ParameterPointer(name) => crate::kernel::symbolic_call_result(
                    ProgramType::ParameterPointer(name),
                    Variable(index as u64),
                ),
                // A slice parameter is one value named by its binder
                // (`design/rust-slice-values.md`).
                InterfaceType::Slice(element) => crate::kernel::symbolic_call_result(
                    ProgramType::SlicePointer(element),
                    Variable(index as u64),
                ),
                InterfaceType::Void => unreachable!("pure theorem parameters cannot be void"),
                // A `Bool` parameter is a binder of the kernel sort (Stage 5),
                // carried as its cast to `uint8` (rule C1).
                InterfaceType::Bool => ProgramValue::Bool(OldMachineTerm::bool_cast(
                    crate::kernel::MachineIntegerType::UInt8,
                    crate::kernel::OldConditionTerm::Variable(Variable(index as u64)),
                )),
                InterfaceType::VoidPointer
                | InterfaceType::VoidPointerPointer
                | InterfaceType::Pointer => ProgramValue::typed_pointer(
                    Address::new(
                        AddressBase::ExternalArgument,
                        scale_int32_offset(
                            OldMachineTerm::Variable(Variable::produced(
                                crate::kernel::Producer::PointerArgument,
                                index as u64,
                            )),
                            1,
                        ),
                    ),
                    interface_type.to_kernel_type(),
                ),
                InterfaceType::Int8 => {
                    ProgramValue::Int8(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Int16 => {
                    ProgramValue::Int16(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Int32 => {
                    ProgramValue::Int32(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::UInt32 => {
                    ProgramValue::UInt32(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Char(crate::languages::c::syntax::PlainChar::Unsigned) => {
                    ProgramValue::UInt8(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Char(crate::languages::c::syntax::PlainChar::Signed) => {
                    ProgramValue::Int8(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::UInt8 => {
                    ProgramValue::UInt8(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::UInt16 => {
                    ProgramValue::UInt16(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Int64(_) => {
                    ProgramValue::Int64(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::UInt64(_) => {
                    ProgramValue::UInt64(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Float32 => {
                    ProgramValue::Float32(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Float64 => {
                    ProgramValue::Float64(OldMachineTerm::Variable(Variable(index as u64)))
                }
                InterfaceType::Int8Pointer | InterfaceType::Int8Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                1,
                            ),
                        ),
                        ProgramType::Int8Pointer,
                    )
                }
                InterfaceType::Int16Pointer | InterfaceType::Int16Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                2,
                            ),
                        ),
                        ProgramType::Int16Pointer,
                    )
                }
                InterfaceType::UInt16Pointer | InterfaceType::UInt16Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                2,
                            ),
                        ),
                        ProgramType::UInt16Pointer,
                    )
                }
                InterfaceType::Int32Pointer | InterfaceType::Int32Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                4,
                            ),
                        ),
                        ProgramType::Int32Pointer,
                    )
                }
                InterfaceType::CharPointer(_)
                | InterfaceType::CharArray(_, _)
                | InterfaceType::UInt8Pointer
                | InterfaceType::UInt8Array(_) => ProgramValue::typed_pointer(
                    Address::new(
                        AddressBase::ExternalArgument,
                        scale_int32_offset(
                            OldMachineTerm::Variable(Variable::produced(
                                crate::kernel::Producer::PointerArgument,
                                index as u64,
                            )),
                            1,
                        ),
                    ),
                    ProgramType::UInt8Pointer,
                ),
                InterfaceType::UInt32Pointer | InterfaceType::UInt32Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                4,
                            ),
                        ),
                        ProgramType::UInt32Pointer,
                    )
                }
                InterfaceType::Int64Pointer(_) | InterfaceType::Int64Array(_, _) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                8,
                            ),
                        ),
                        ProgramType::Int64Pointer,
                    )
                }
                InterfaceType::Int128Pointer | InterfaceType::Int128Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                16,
                            ),
                        ),
                        ProgramType::Int128Pointer,
                    )
                }
                InterfaceType::UInt64Pointer(_) | InterfaceType::UInt64Array(_, _) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                8,
                            ),
                        ),
                        ProgramType::UInt64Pointer,
                    )
                }
                InterfaceType::UInt128Pointer | InterfaceType::UInt128Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                16,
                            ),
                        ),
                        ProgramType::UInt128Pointer,
                    )
                }
                InterfaceType::Float32Pointer | InterfaceType::Float32Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                4,
                            ),
                        ),
                        ProgramType::Float32Pointer,
                    )
                }
                InterfaceType::Float64Pointer | InterfaceType::Float64Array(_) => {
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                8,
                            ),
                        ),
                        ProgramType::Float64Pointer,
                    )
                }
                InterfaceType::Int8PointerPointer => {
                    let element_width = interface_type
                        .pointee_type()
                        .expect("pointer-to-pointer parameter has a pointee")
                        .to_kernel_type()
                        .byte_width();
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                i64::from(element_width),
                            ),
                        ),
                        interface_type.to_kernel_type(),
                    )
                }
                InterfaceType::Int32PointerPointer
                | InterfaceType::CharPointerPointer(_)
                | InterfaceType::UInt8PointerPointer
                | InterfaceType::Int16PointerPointer
                | InterfaceType::UInt16PointerPointer
                | InterfaceType::UInt32PointerPointer
                | InterfaceType::Int128PointerPointer
                | InterfaceType::Int64PointerPointer(_)
                | InterfaceType::UInt128PointerPointer
                | InterfaceType::UInt64PointerPointer(_)
                | InterfaceType::Float32PointerPointer
                | InterfaceType::Float64PointerPointer => {
                    let element_width = interface_type
                        .pointee_type()
                        .expect("pointer-to-pointer parameter has a pointee")
                        .to_kernel_type()
                        .byte_width();
                    ProgramValue::typed_pointer(
                        Address::new(
                            AddressBase::ExternalArgument,
                            scale_int32_offset(
                                OldMachineTerm::Variable(Variable::produced(
                                    crate::kernel::Producer::PointerArgument,
                                    index as u64,
                                )),
                                i64::from(element_width),
                            ),
                        ),
                        interface_type.to_kernel_type(),
                    )
                }
                InterfaceType::FunctionPointer(_) => ProgramValue::typed_pointer(
                    Address::symbolic_function(Variable(index as u64)),
                    interface_type.to_kernel_type(),
                ),
                InterfaceType::PointerArray(_, _, _) => ProgramValue::typed_pointer(
                    Address::new(
                        AddressBase::ExternalArgument,
                        scale_int32_offset(
                            OldMachineTerm::Variable(Variable::produced(
                                crate::kernel::Producer::PointerArgument,
                                index as u64,
                            )),
                            8,
                        ),
                    ),
                    interface_type.to_kernel_type(),
                ),
            };
            let value = if generic_pointers.contains(parameter.name()) {
                match value {
                    ProgramValue::Pointer(pointer) => ProgramValue::Pointer(
                        pointer.with_declared_object_class(parameter.pointer_object_class()),
                    ),
                    value => value,
                }
            } else {
                value.with_pointer_object_class(parameter.pointer_object_class())
            };
            Some((parameter.name().to_string(), value))
        })
        .collect()
}

pub(in crate::surface) fn pure_theorem_array_refs(
    parameters: &[FunctionParameter],
    values: &ProgramValueBindings,
    point: &crate::kernel::ProgramPoint,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let interface_type = parameter.click_type().interface_type()?;
            let element_type = click_array_element_type(interface_type)?;
            let Some(ProgramValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    point: point.clone(),
                    pointer: pointer.address().clone(),
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
    function_environment: Option<&ExecutionEnvironment>,
) -> Result<VerifiedPureTheorem, ClickError> {
    let _automation_scope = super::implicit_solve_scope::ClaimScope::enter(claim_label);
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
        )
        .with_proof_refusal(ProofRefusal::Contract));
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
    let state = ExecutionState::at_point(&context.point);
    let (goal, goal_introductions, _, obligations) =
        lower_stated_proposition_retaining_requirements(
            surface_goal,
            &PureFactContext::new(),
            ContractEnvironment::new(&context.values, &context.array_refs),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            spec_definitions,
            FixedStateLoweringOptions {
                integer_values: Some(&context.integer_values),
                obligation_assumptions: Some(&lowering_assumptions),
                ..Default::default()
            },
        )
        .map_err(|reason| {
            let diagnostic = ClickError::new(format!(
                "`{claim_label}` failed: could not lower conclusion: pure theorem `{}`: {reason}",
                theorem.name()
            ));
            theorem_statement_error(diagnostic, reason)
        })?;
    // This probe checks only retained requirements, not a proof operation.
    // No unchecked successor or theorem authority is produced here.
    let (entry_check, entry_requirements) =
        super::execution_planning::probe_open_obligations(|| {
            super::fixed_state_proofs::conversion_conditions::refuse_unproved_conversion_bounds(
                &obligations,
                &lowering_assumptions,
                &super::fixed_state_proofs::conversion_conditions::StatedSite::new(
                    super::fixed_state_proofs::conversion_conditions::StatedForm::Proposition(
                        surface_goal,
                    ),
                    &state,
                    &context.values,
                )
                .with_integer_values(&context.integer_values),
            )
        });

    entry_check
        .map_err(|message| ClickError::new(message).with_proof_refusal(ProofRefusal::Contract))?;

    if theorem.is_axiom() {
        // A Click library axiom is trusted: it states what the library's
        // primitive operations mean, as the kernel's integer laws do for its
        // integers. Its domains are still checked, as an ordinary theorem's.
        let root = Proof::for_pure_surface_goal(
            claim_label,
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            context,
            spec_definitions,
            theorem_environment,
        );
        root.driver()
            .discharge_entry_requirements(surface_goal, &entry_requirements)?;
        return Ok(VerifiedPureTheorem {
            theorem_definition: theorem.clone(),
            ensure_index,
            ensure_clause: ensure_clause.clone(),
            proof_kind: ProofKind::Axiom,
            proof: None,
            contract_value_parameters: None,
            requires: context.requires.clone(),
            conclusion: goal,
            kernel_authority: None,
            checked_completion: None,
        });
    }

    if is_kernel_standard_theorem_name(theorem.name()) {
        // A registered axiom supplies the conclusion, not permission to
        // evaluate partial syntax in its declaration. Check those domains
        // through the same proof entry operation as ordinary theorems.
        let root = Proof::for_pure_surface_goal(
            claim_label,
            &context.requires,
            goal.clone(),
            surface_goal.clone(),
            context,
            spec_definitions,
            theorem_environment,
        );
        root.driver()
            .discharge_entry_requirements(surface_goal, &entry_requirements)?;
        return verify_kernel_standard_theorem_axiom(
            theorem,
            ensure_index,
            ensure_clause,
            claim_label,
            context,
            goal,
            spec_definitions,
        );
    }

    let (proof_kind, certificate, checked_completion) = match ensure_clause.proof() {
        SourceProof::Default
        | SourceProof::Tactic(SmartTactic::ImplicitTail | SmartTactic::Solve) => {
            let (certificate, completion) = check_direct_pure_goal_with_proof(
                !matches!(ensure_clause.proof(), SourceProof::Default),
                matches!(
                    ensure_clause.proof(),
                    SourceProof::Tactic(SmartTactic::ImplicitTail)
                ),
                claim_label,
                context,
                surface_goal,
                &goal,
                &goal_introductions,
                &entry_requirements,
                spec_definitions,
                theorem_environment,
            )?;
            let kind = if matches!(
                ensure_clause.proof(),
                SourceProof::Tactic(SmartTactic::Solve)
            ) {
                ProofKind::Solve
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
            let setup = prepare_pure_induction_setup(
                theorem,
                surface_goal,
                tactics,
                context,
                spec_definitions,
            )?;
            let (certificate, completion) = check_pure_script_with_proof(
                claim_label,
                context,
                surface_goal,
                &goal,
                &goal_introductions,
                &entry_requirements,
                tactics,
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
    };
    let kernel_variables = theorem
        .parameters()
        .iter()
        .map(|parameter| match context.values.get(parameter.name()) {
            Some(ProgramValue::Int32(OldMachineTerm::Variable(variable))) => Some(*variable),
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
        contract_value_parameters: spec_definitions
            .predicates
            .contract_value_parameters
            .clone(),
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

fn refinement_preparation_error(
    error: crate::kernel::ContractRefinementPreparationError,
) -> ClickError {
    use crate::kernel::{ContractRefinementPreparationError as PreparationError, ExecutionLimit};
    use crate::surface::{ClickErrorKind, ProofRefusal};

    match error {
        PreparationError::Unsupported(detail) => {
            ClickError::new(detail).with_kind(ClickErrorKind::Unsupported)
        }
        PreparationError::Incompatible(detail) => {
            ClickError::new(detail).with_proof_refusal(ProofRefusal::Contract)
        }
        PreparationError::Evaluation { clause, detail } => {
            let message = match detail {
                Some(detail) => format!("could not evaluate {clause}: {detail}"),
                None => format!("could not evaluate {clause}"),
            };
            ClickError::new(message).with_proof_refusal(ProofRefusal::IncompleteProof)
        }
        PreparationError::Stopped(stop) => {
            let error = ClickError::new(format!(
                "preparing refinement obligations stopped at {}",
                stop.describe()
            ));
            match stop {
                ExecutionLimit::ExecutionIdentityBesideLiveState
                | ExecutionLimit::QuantifierDoesNotClose => {
                    error.with_kind(ClickErrorKind::Internal)
                }
                ExecutionLimit::Deadline
                | ExecutionLimit::ExpressionSteps
                | ExecutionLimit::StatementSteps
                | ExecutionLimit::FunctionCalls
                | ExecutionLimit::LoopUnrolls
                | ExecutionLimit::KernelVariables { .. }
                | ExecutionLimit::MatchBinderVariables { .. } => {
                    error.with_kind(ClickErrorKind::Internal)
                }
                ExecutionLimit::UnsupportedPureFunctionResult(ProgramType::Void)
                | ExecutionLimit::BoolComparedWithInteger
                | ExecutionLimit::BoolOrdered
                | ExecutionLimit::BoolArithmetic
                | ExecutionLimit::MixedBoolArms => error.with_kind(ClickErrorKind::Type),
                ExecutionLimit::GuardedConjunctionTooLong
                | ExecutionLimit::SymbolicPointerConditional => {
                    error.with_kind(ClickErrorKind::Unsupported)
                }
                ExecutionLimit::UnsupportedPureFunctionResult(_) => {
                    error.with_kind(ClickErrorKind::Internal)
                }
                ExecutionLimit::Paths
                | ExecutionLimit::LoopIterationsUnbound
                | ExecutionLimit::ResourceFieldInstanceUnavailable
                | ExecutionLimit::AuthorityCountNeedsExactPointer
                | ExecutionLimit::AuthorityCountNeedsResolvedMember
                | ExecutionLimit::AuthorityCountNeedsOwnership
                | ExecutionLimit::AuthorityCountLentToWorker
                | ExecutionLimit::AuthorityCountPendingLockedWorker
                | ExecutionLimit::DisjunctionRightUndefined => {
                    error.with_proof_refusal(ProofRefusal::IncompleteProof)
                }
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn verify_contract_refinement_theorem(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    surface_goal: &SyntaxProposition,
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
    theorem_environment: &TheoremEnvironment,
    function_environment: Option<&ExecutionEnvironment>,
) -> Result<Option<VerifiedPureTheorem>, ClickError> {
    use super::smart_closures::LinearScriptDecline;
    use crate::surface::{ClickErrorKind, ProofRefusal};

    let SyntaxProposition::PredicateCall { name, arguments } = surface_goal else {
        return Ok(None);
    };
    let Some(contract_definition) = spec_definitions.predicates.contract_definition(name) else {
        return Ok(None);
    };
    // The function value, then the values of the contract's value
    // parameters.
    let Some(argument) = arguments.first() else {
        return Ok(None);
    };
    let lower = |proposition: &SyntaxProposition| {
        lower_pure_theorem_proposition_with_integer_values(
            theorem.name(),
            proposition,
            ContractEnvironment::new(&context.values, &context.array_refs),
            &context.integer_values,
            &context.point,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` failed: could not lower conclusion: {message}"
            ))
        })
    };
    let goal = lower(surface_goal)?;
    let target_values = contract_fact_values(&goal).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}`: `{name}` expects a function pointer and its {} value parameter(s)",
            contract_definition.value_parameters().len()
        ))
    })?;
    let concrete_target = contract_expression_function_address(argument);
    let symbolic_binding = match argument {
        SyntaxTerm::Binding(name)
        | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => Some(name.as_str()),
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
        if parameter.name() != binding
            || !matches!(
                parameter.interface_type(),
                InterfaceType::FunctionPointer(_)
            )
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
        let Some(SyntaxProposition::PredicateCall {
            name: source_name,
            arguments: source_arguments,
        }) = requirement.proposition()
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: abstract contract refinement requires a source-contract proposition"
            )));
        };
        let Some(source_argument) = source_arguments.first() else {
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
        let source_values = contract_fact_values(&lower(
            requirement
                .proposition()
                .expect("the source requirement is a proposition"),
        )?)
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}`: `{source_name}` expects a function pointer and its {} value \
                 parameter(s)",
                source_definition.value_parameters().len()
            ))
        })?;
        Some((source_name.as_str(), source_definition, source_values))
    };
    let SourceProof::Script(tactics) = ensure_clause.proof() else {
        let subject = concrete_target
            .map(|target| format!("&{target}"))
            .or_else(|| symbolic_binding.map(str::to_string))
            .expect("a refinement theorem has a recognized subject");
        return Err(ClickError::new(format!(
            "`{claim_label}`: proving `{name}({subject})` requires an explicit contract-refinement proof"
        )).with_proof_refusal(ProofRefusal::IncompleteProof));
    };
    // Contract refinement opens explicitly selected contract applications.
    // Compare the lowered applications, including callback and value arguments.
    let selected_application = |tactic: &ProofTactic| -> Result<Option<Proposition>, ClickError> {
        let target = match tactic {
            ProofTactic::UnfoldProposition(target) => target.clone(),
            ProofTactic::UnfoldFunction(application) => SyntaxProposition::PredicateCall {
                name: application.name.clone(),
                arguments: application.arguments.clone(),
            },
            _ => return Ok(None),
        };
        lower(&target).map(Some)
    };
    let count = if source_contract.is_some() { 2 } else { 1 };
    let Some((prefix, proof_tactics)) = tactics.split_at_checked(count) else {
        return Err(ClickError::new(format!(
            "`{claim_label}`: contract refinement must begin by unfolding its selected contract applications"
        )).with_proof_refusal(ProofRefusal::IncompleteProof));
    };
    let mut expected = vec![goal.clone()];
    if source_contract.is_some() {
        expected.push(lower(
            theorem.requires()[0]
                .proposition()
                .expect("source contract requirement"),
        )?);
    }
    for tactic in prefix {
        let Some(selected) = selected_application(tactic)? else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: contract refinement requires explicit `unfold(contract(callback))` applications"
            )).with_proof_refusal(ProofRefusal::Tactic).with_failed_tactic(tactic_name(tactic)));
        };
        let Some(index) = expected
            .iter()
            .position(|value| crate::kernel::proof::propositions_are_alpha_equal(value, &selected))
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}`: unfold selects a different contract application"
            ))
            .with_proof_refusal(ProofRefusal::Tactic)
            .with_failed_tactic(tactic_name(tactic)));
        };
        expected.remove(index);
    }
    let function_environment = function_environment.ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}`: contract-refinement theorems require the C function environment"
        ))
    })?;
    let refinement = match (concrete_target, &source_contract) {
        (Some(target), None) => {
            crate::kernel::program_function_contract_refinement_context_reporting(
                function_environment, name, spec_definitions.predicates.function_execution_name(target), &target_values,
            )
            .map_err(|refusal| {
                use crate::kernel::ConcreteRefinementRefusal::*;
                let (detail, internal) = match refusal {
                    MissingContract => ("the named contract is missing from the checked environment", true),
                    InvalidContractArguments => ("the named contract's value arguments could not be bound", true),
                    MissingTarget => ("the target has no verified or external contract in scope", false),
                    ThrowingTarget => ("the target may throw, but the named contract promises it cannot throw", false),
                    DifferentExceptionType => ("the target and named contract declare different exception payload types", false),
                    IncompatibleInterface => ("the signatures or resource interfaces are incompatible", false),
                    ContextUnavailable => ("Click could not prepare refinement for the compatible interfaces", true),
                };
                let error = ClickError::new(format!(
                    "`{claim_label}`: `{target}` is not a verified or external function compatible with contract `{name}`: {detail}"
                ));
                if internal {
                    error.with_kind(ClickErrorKind::Internal)
                } else {
                    error.with_proof_refusal(ProofRefusal::Tactic).with_failed_tactic("unfold")
                }
            })?
        }
        (None, Some((source_name, _, source_values))) => {
            let binding = symbolic_binding.expect("abstract refinement has a callback binding");
            let pointer = context.values.get(binding).ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}`: symbolic callback `{binding}` has no theorem value"
                ))
            })?;
            contract_refinement_context(
                function_environment,
                name,
                &target_values,
                source_name,
                source_values,
                pointer,
            )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}`: contract `{source_name}` is not signature-compatible with `{name}`"
                    ))
                })?
        }
        _ => unreachable!("refinement subject classification is exhaustive"),
    };
    let argument_values = program_function_contract_refinement_arguments(&refinement);
    // The contract's value parameters trail its call parameters; the
    // refinement binds them to the conclusion's values.
    let all_parameters = contract_definition
        .function_block()
        .signature()
        .parameters();
    let contract_parameters = &all_parameters[..all_parameters
        .len()
        .saturating_sub(contract_definition.value_parameters().len())];
    if contract_parameters.len() != argument_values.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}`: contract parameter count does not match its lowered function"
        )));
    }
    let subject = concrete_target
        .map(|target| format!("&{target}"))
        .or_else(|| symbolic_binding.map(str::to_string))
        .expect("refinement subject");
    let summary = format!(
        "`{claim_label}`: contract-refinement proof does not establish `{name}({subject})`"
    );
    let obligations =
        check_program_function_contract_refinement_obligations(&refinement).map_err(|error| {
            refinement_preparation_error(error)
                .at_declaration(theorem.name())
                .with_context(&summary)
        })?;
    let arguments = argument_values
        .iter()
        .cloned()
        .map(ProgramExpression::Value)
        .collect::<Vec<_>>();
    let parameters = contract_parameters
        .iter()
        .map(|parameter| {
            crate::languages::interface::ImportedParameter::new(
                parameter.interface_type(),
                parameter.name().to_string(),
                parameter.struct_name().map(str::to_string),
            )
        })
        .collect::<Vec<_>>();
    // The refinement's clauses are written in the contract's scope: its
    // parameters and its result, with no locals.
    let contract_signature = contract_definition.function_block().signature();
    let contract_scope_function = crate::languages::interface::ImportedFunction::external(
        contract_signature.return_type(),
        contract_signature.name().to_string(),
        parameters.clone(),
    )
    .with_spelled_local_types(BTreeMap::new());
    let proof_goal = obligations.proposition().clone();
    let mut presentation =
        super::surface_synthesis::synthesize_surface_proposition_at_entry_and_post(
            &proof_goal,
            ParameterBinding::new(&parameters, &arguments),
            obligations.entry(),
            obligations.post(),
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}`: cannot present contract-refinement obligations"
            ))
            .with_kind(ClickErrorKind::Internal)
        })?;
    // Expansion prints this presentation as source. A native comparison over
    // arithmetic is spelled through its Integer observations, as written
    // arithmetic in a comparison reads exactly; spelled bare, `result ==
    // (x + 3)` would parse back as `to_integer(result) == to_integer(x) + 3`.
    super::surface_synthesis::spell_conjunct_observations(&proof_goal, &mut presentation);
    let retained_states = RecordedStates::new();
    let mut surfaces = SurfacePropositionMap::default();
    let mut pending = vec![(&proof_goal, &presentation)];
    while let Some((kernel, surface)) = pending.pop() {
        match (kernel, surface) {
            (Proposition::And(kl, kr), SyntaxProposition::And(sl, sr))
            | (Proposition::Or(kl, kr), SyntaxProposition::Or(sl, sr))
            | (Proposition::Implies(kl, kr), SyntaxProposition::Implies(sl, sr)) => {
                pending.push((kl, sl));
                pending.push((kr, sr));
            }
            (Proposition::Not(k), SyntaxProposition::Not(s)) => pending.push((k, s)),
            _ => surfaces.record_lowering(surface, kernel)?,
        }
    }
    // FixedStateFrame still has an explicit native result presentation boundary.
    let result = obligations
        .post()
        .locals()
        .get_native(crate::kernel::CONTRACT_RESULT);
    let root = Proof::for_contract_refinement_goal(
        claim_label,
        proof_goal,
        presentation,
        ParameterBinding::new(&parameters, &arguments),
        obligations.entry(),
        obligations.post(),
        result.as_deref(),
        &retained_states,
        &surfaces,
        spec_definitions,
        theorem_environment,
    )
    .with_clause_scope(ClauseScope {
        function: &contract_scope_function,
        bindings: None,
    });
    let mut search = super::attempt::search_scope("contract refinement");
    let mut declined = None;
    let mut unfinished = None;
    let sites = claim_script_sites(&root, proof_tactics, count);
    let attempted = match root.driver().try_addressed_linear_script(
        proof_tactics,
        &sites,
        &mut declined,
        Some(&mut unfinished),
        true,
    ) {
        Ok(attempted) => attempted,
        Err(error) => {
            return Err(error
                .with_context(&summary)
                .with_search_failures(search.finish()));
        }
    };
    let Some(proof) = attempted else {
        check_verification_deadline()?;
        let focused = unfinished.as_ref().unwrap_or(&root);
        let error = match declined {
            Some(LinearScriptDecline::Shape) => focused
                .step_error("the proof ended without proving the refinement obligations")
                .with_proof_refusal(ProofRefusal::IncompleteProof),
            Some(
                LinearScriptDecline::Step(index) | LinearScriptDecline::UnsuccessfulSearch(index),
            ) => {
                let refusal = match declined {
                    Some(LinearScriptDecline::UnsuccessfulSearch(_)) => {
                        ProofRefusal::UnsuccessfulSearch
                    }
                    _ => ProofRefusal::Tactic,
                };
                focused
                    .at_site(&sites[index])
                    .step_error(format!(
                        "could not complete `{}`",
                        tactic_name(&proof_tactics[index])
                    ))
                    .with_proof_refusal(refusal)
            }
            None => focused
                .step_error("the proof ended with a refinement obligation still open")
                .with_proof_refusal(ProofRefusal::IncompleteProof),
        };
        return Err(error
            .with_context(&summary)
            .with_search_failures(search.finish()));
    };
    search.succeed();
    let checked = proof.completed_proposition()?;
    let kernel_authority =
        prove_program_function_contract_refinement(&obligations, goal.clone(), &checked)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "{summary}: Click could not issue a theorem from the completed proof of the refinement obligations"
                ))
                .with_kind(ClickErrorKind::Internal)
            })?;
    let mut certificate_steps =
        ProofCertificate::from_proof_tactics(&tactics[..tactics.len() - proof_tactics.len()])
            .map_err(|error| ClickError::new(format!("{error}")))?
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
        contract_value_parameters: spec_definitions
            .predicates
            .contract_value_parameters
            .clone(),
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority: Some(kernel_authority),
        checked_completion: None,
    }))
}

/// The values a lowered contract fact fixes its contract's value parameters
/// to, after its function pointer. `None` for any other proposition, or a
/// value that is not a C value.
fn contract_fact_values(fact: &Proposition) -> Option<Vec<ProgramValue>> {
    let Proposition::Predicate { arguments, .. } = fact else {
        return None;
    };
    arguments
        .get(2..)?
        .iter()
        .map(|argument| match argument {
            Term::ProgramValue(value) => Some(value.old_form().clone()),
            _ => None,
        })
        .collect()
}

/// Lets direct smart pure proofs search by applying checked proof steps.
///
/// Failed descendants are simply discarded. A successful descendant already
/// owns both the semantic successor and the exact simple certificate that
/// produced it, so ordinary operation does not reconstruct and check that
/// certificate through the legacy gateway.
/// The ordered int32 equalities a rewrite certificate ending in `known` cites.
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
    if !matches!(closer, [ProofStep::Known]) || rewrite_steps.is_empty() {
        return None;
    }
    rewrite_steps
        .iter()
        .map(|step| match step {
            ProofStep::Rewrite(surface) => lower_pure_theorem_proposition(
                claim_label,
                surface,
                ContractEnvironment::new(&context.values, &context.array_refs),
                &context.point,
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
pub(super) fn claim_script_sites(
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
    implicit: bool,
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &SyntaxProposition,
    goal: &Proposition,
    goal_introductions: &crate::kernel::LoweringIntroductions,
    entry_requirements: &super::execution_planning::OpenObligationProbe,
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
    let root = root
        .driver()
        .discharge_entry_requirements(surface_goal, entry_requirements)?;
    let mut search = super::attempt::search_scope("pure theorem solve");
    // Default proof search has a budget and timing, but no written tactic
    // occurrence. Its failure belongs to the declaration, not a fabricated
    // `solve` site at the ensures clause.
    let (root, _timing) = if has_written_tactic {
        (
            root.at_source_tactic(0),
            TacticTiming::pure_source(claim_label, vec![0], &ProofTactic::Solve),
        )
    } else {
        (
            root,
            TacticTiming::new(claim_label, 0, 0, &ProofTactic::Solve, 0),
        )
    };
    use crate::surface::proof_trace::TraceOrigin;
    let _origin = if implicit {
        TraceOrigin::enter_implicit("implicit tail")
    } else {
        TraceOrigin::enter(Some("solve"))
    };
    let (result, checks) = crate::surface::proof_diagnostics::capture_check_observations(|| {
        crate::kernel::search::ProofSearch::try_solve_closure(&root)
    });
    let result = match result {
        Ok(result) => result,
        Err(error) => {
            return Err(error
                .with_check_observations(checks)
                .with_search_failures(search.finish()));
        }
    };
    let Some(proof) = result else {
        return Err(root
            .solve_failure()
            .with_check_observations(checks)
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

fn is_nat_integer_law_name(name: &str) -> bool {
    matches!(
        name,
        "click::nat::to_integer_zero"
            | "click::nat::to_integer_succ"
            | "click::nat::to_integer_nonnegative"
            | "click::nat::to_nat_to_integer"
            | "click::nat::to_integer_to_nat"
            | "click::nat::to_nat_zero"
    )
}

fn resource_law_shape(name: &str) -> Option<(usize, usize)> {
    Some(match name {
        "click::separation::contains_refl" | "click::separation::separate_emp" => (1, 0),
        "click::separation::contains_left" | "click::separation::contains_right" => (2, 0),
        "click::separation::contains_trans" | "click::separation::separate_star" => (3, 2),
        "click::separation::separate_symm" => (2, 1),
        "click::separation::viewable_restrict" => (2, 2),
        _ => return None,
    })
}

pub(in crate::surface) fn is_kernel_standard_theorem_name(name: &str) -> bool {
    resource_law_shape(name).is_some()
        || name == "click::integer::uint32_from_le_bytes"
        || name == "click::separation::separate_restrict"
        || matches!(
            name.split("::<").next(),
            Some(
                "click::separation::contains_subrange"
                    | "click::separation::contains_element"
                    | "click::separation::contains_rebase"
                    | "click::separation::contains_joined_ranges"
                    | "click::separation::separate_adjacent_ranges"
                    | "click::separation::separate_elements"
                    | "click::separation::distinct_elements"
            )
        )
        || crate::kernel::integer_truncation_law_requirements(name).is_some()
        || is_nat_integer_law_name(name)
        || matches!(
            name,
            "click::integer::int32_remainder_to_integer"
                | "click::integer::uint64_pack_uint16_to_integer"
                | "click::integer::uint64_unpack_uint16_low"
                | "click::integer::uint64_unpack_uint16_high"
                | "click::integer::uint32_pack_uint16_to_integer"
                | "click::integer::uint32_pack_uint16_high_first_to_integer"
                | "click::integer::uint32_unpack_uint16_low"
                | "click::integer::uint32_unpack_uint16_high"
                | "click::integer::uint64_divide_to_integer"
                | "click::integer::uint64_remainder_to_integer"
                | "int32_le_antisymmetric"
                | "click::integer::uint32_divide_to_integer"
                | "click::integer::uint32_remainder_to_integer"
        )
}

fn verify_kernel_standard_theorem_axiom(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    goal: Proposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<VerifiedPureTheorem, ClickError> {
    let (parameter_count, requirement_count) = match theorem.name() {
        name if resource_law_shape(name).is_some() => resource_law_shape(name).unwrap(),
        "click::integer::uint32_from_le_bytes" => (1, 3),
        "click::separation::separate_restrict" => (4, 3),
        name if name.split("::<").next() == Some("click::separation::contains_subrange") => (5, 3),
        name if name.split("::<").next() == Some("click::separation::contains_element") => (4, 2),
        name if name.split("::<").next() == Some("click::separation::contains_rebase") => (3, 2),
        name if matches!(
            name.split("::<").next(),
            Some(
                "click::separation::separate_adjacent_ranges"
                    | "click::separation::contains_joined_ranges"
            )
        ) =>
        {
            (4, 2)
        }
        name if matches!(
            name.split("::<").next(),
            Some("click::separation::separate_elements" | "click::separation::distinct_elements")
        ) =>
        {
            (3, 1)
        }
        "click::nat::to_integer_zero" | "click::nat::to_nat_zero" => (0, 0),
        "click::nat::to_integer_succ"
        | "click::nat::to_integer_nonnegative"
        | "click::nat::to_nat_to_integer" => (1, 0),
        "click::nat::to_integer_to_nat" => (1, 1),
        name if crate::kernel::integer_truncation_law_requirements(name).is_some() => (
            2,
            crate::kernel::integer_truncation_law_requirements(name).unwrap(),
        ),
        "click::integer::uint64_pack_uint16_to_integer"
        | "click::integer::uint64_unpack_uint16_low"
        | "click::integer::uint64_unpack_uint16_high"
        | "click::integer::uint32_pack_uint16_to_integer"
        | "click::integer::uint32_pack_uint16_high_first_to_integer"
        | "click::integer::uint32_unpack_uint16_low"
        | "click::integer::uint32_unpack_uint16_high"
        | "click::integer::uint64_divide_to_integer"
        | "click::integer::uint64_remainder_to_integer"
        | "click::integer::uint32_divide_to_integer"
        | "click::integer::uint32_remainder_to_integer" => (2, 2),
        "click::integer::int32_remainder_to_integer" => (2, 2),
        "int32_le_antisymmetric" => (2, 2),
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
    let axiom = if theorem.name() == "click::integer::uint32_from_le_bytes" {
        let Some(ProgramValue::Pointer(pointer)) =
            context.values.get(theorem.parameters()[0].name())
        else {
            return Err(ClickError::new(
                "uint32_from_le_bytes requires a uint32 pointer",
            ));
        };
        crate::kernel::prove_uint32_from_le_bytes(pointer.clone()).map_err(ClickError::new)?
    } else if let Some(
        law @ ("click::separation::separate_elements" | "click::separation::distinct_elements"),
    ) = theorem.name().split("::<").next()
    {
        let parameter = |index: usize| match context.values.get(theorem.parameters()[index].name())
        {
            Some(ProgramValue::Int32(value)) => Ok((MachineIntegerType::Int32, value.clone())),
            Some(ProgramValue::Int64(value)) => Ok((MachineIntegerType::Int64, value.clone())),
            Some(ProgramValue::UInt64(value)) => Ok((MachineIntegerType::UInt64, value.clone())),
            _ => Err(ClickError::new(
                "elements indices must be int32, int64, or uint64",
            )),
        };
        let Some(ProgramValue::Pointer(pointer)) =
            context.values.get(theorem.parameters()[0].name())
        else {
            return Err(ClickError::new("elements base must be a typed pointer"));
        };
        let width = spec_definitions
            .pointer_element_width(pointer)
            .map_err(ClickError::new)?;
        if width == 0 {
            return Err(ClickError::new("elements requires a nonzero element width"));
        }
        let (format, i) = parameter(1)?;
        let (other_format, j) = parameter(2)?;
        if format != other_format {
            return Err(ClickError::new("elements indices must have the same type"));
        }
        if law == "click::separation::separate_elements" {
            crate::kernel::prove_separation_elements(pointer.clone(), width, format, i, j)
        } else {
            crate::kernel::prove_separation_distinct_elements(pointer.clone(), width, format, i, j)
        }
    } else if matches!(
        theorem.name().split("::<").next(),
        Some(
            "click::separation::contains_subrange"
                | "click::separation::contains_element"
                | "click::separation::contains_rebase"
                | "click::separation::contains_joined_ranges"
                | "click::separation::separate_adjacent_ranges"
        )
    ) {
        let parameter = |index: usize| match context.values.get(theorem.parameters()[index].name())
        {
            Some(ProgramValue::Int32(value)) => Ok((MachineIntegerType::Int32, value.clone())),
            Some(ProgramValue::UInt64(value)) => Ok((MachineIntegerType::UInt64, value.clone())),
            _ => Err(ClickError::new(
                "interval law bounds must be int32 or uint64",
            )),
        };
        let Some(ProgramValue::Pointer(pointer)) =
            context.values.get(theorem.parameters()[0].name())
        else {
            return Err(ClickError::new("interval law base must be a typed pointer"));
        };
        let width = spec_definitions
            .pointer_element_width(pointer)
            .map_err(ClickError::new)?;
        if width == 0 {
            return Err(ClickError::new(
                "interval law requires a nonzero element width",
            ));
        }
        let bounds = (1..theorem.parameters().len())
            .map(parameter)
            .collect::<Result<Vec<_>, _>>()?;
        let format = bounds[0].0;
        if bounds.iter().any(|(kind, _)| *kind != format) {
            return Err(ClickError::new(
                "interval law bounds must have the same type",
            ));
        }
        let law = theorem.name().split("::<").next();
        if matches!(
            law,
            Some(
                "click::separation::separate_adjacent_ranges"
                    | "click::separation::contains_joined_ranges"
            )
        ) {
            crate::kernel::prove_separation_adjacent_ranges(
                pointer.clone(),
                width,
                format,
                bounds[0].1.clone(),
                bounds[1].1.clone(),
                bounds[2].1.clone(),
                law == Some("click::separation::contains_joined_ranges"),
            )
        } else if theorem.name().split("::<").next() == Some("click::separation::contains_rebase") {
            crate::kernel::prove_separation_rebase(
                pointer.clone(),
                width,
                format,
                bounds[0].1.clone(),
                bounds[1].1.clone(),
            )
        } else if theorem.name().split("::<").next() == Some("click::separation::contains_element")
        {
            crate::kernel::prove_separation_contains_element(
                pointer.clone(),
                width,
                format,
                bounds[0].1.clone(),
                bounds[1].1.clone(),
                bounds[2].1.clone(),
            )
        } else {
            crate::kernel::prove_separation_subrange(
                pointer.clone(),
                width,
                format,
                bounds[0].1.clone(),
                bounds[1].1.clone(),
                bounds[2].1.clone(),
                bounds[3].1.clone(),
            )
        }
    } else if resource_law_shape(theorem.name()).is_some() {
        if theorem
            .parameters()
            .iter()
            .any(|p| p.click_type() != &ClickType::Resource)
        {
            return Err(ClickError::new(
                "separation law parameters must be Resource",
            ));
        }
        let args = (0..theorem.parameters().len())
            .map(|i| crate::kernel::Resource::Parameter(Variable(i as u64)))
            .collect::<Vec<_>>();
        if theorem.name() == "click::separation::viewable_restrict" {
            crate::kernel::prove_viewable_restrict(
                context.point.memory(),
                context.point.path_link().clone(),
                args[0].clone(),
                args[1].clone(),
            )
        } else {
            crate::kernel::prove_resource_law(theorem.name(), &args)
                .expect("registered resource law")
        }
    } else if theorem.name() == "click::separation::separate_restrict" {
        if theorem
            .parameters()
            .iter()
            .any(|p| p.click_type() != &ClickType::Resource)
        {
            return Err(ClickError::new(
                "separation::separate_restrict parameters must be Resource",
            ));
        }
        crate::kernel::prove_separation_restrict(
            crate::kernel::Resource::Parameter(Variable(0)),
            crate::kernel::Resource::Parameter(Variable(1)),
            crate::kernel::Resource::Parameter(Variable(2)),
            crate::kernel::Resource::Parameter(Variable(3)),
        )
    } else if crate::kernel::integer_truncation_law_requirements(theorem.name()).is_some() {
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
    } else if theorem
        .name()
        .rsplit("::")
        .next()
        .is_some_and(|name| name.starts_with("uint64_"))
    {
        let parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(ProgramValue::UInt64(value)) => Ok(value.clone()),
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be uint64",
                    parameter.name()
                ))),
            }
        };
        crate::kernel::prove_uint64_integer_bridge(theorem.name(), parameter(0)?, parameter(1)?)
            .expect("registered uint64 observation bridge")
    } else if theorem
        .name()
        .rsplit("::")
        .next()
        .is_some_and(|name| name.starts_with("uint32_"))
    {
        let uint32_parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(ProgramValue::UInt32(term)) => Ok(term.clone()),
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be uint32",
                    parameter.name()
                ))),
            }
        };
        let value = uint32_parameter(0)?;
        match theorem.name() {
            "click::integer::uint32_unpack_uint16_low" => {
                crate::kernel::prove_uint32_unpack_uint16_low(value, uint32_parameter(1)?)
            }
            "click::integer::uint32_unpack_uint16_high" => {
                crate::kernel::prove_uint32_unpack_uint16_high(value, uint32_parameter(1)?)
            }
            "click::integer::uint32_pack_uint16_high_first_to_integer" => {
                crate::kernel::prove_unsigned_pack_u16_high_first_to_integer(
                    crate::kernel::MachineIntegerType::UInt32,
                    value,
                    uint32_parameter(1)?,
                )
                .expect("registered unsigned packing law")
            }
            "click::integer::uint32_pack_uint16_to_integer" => {
                crate::kernel::prove_unsigned_pack_u16_to_integer(
                    crate::kernel::MachineIntegerType::UInt32,
                    value,
                    uint32_parameter(1)?,
                )
                .expect("registered unsigned packing law")
            }
            "click::integer::uint32_divide_to_integer" => {
                crate::kernel::prove_uint32_divide_to_integer(value, uint32_parameter(1)?)
            }
            "click::integer::uint32_remainder_to_integer" => {
                crate::kernel::prove_uint32_remainder_to_integer(value, uint32_parameter(1)?)
            }
            _ => unreachable!("checked above"),
        }
    } else {
        let int32_parameter = |index: usize| {
            let parameter = &theorem.parameters()[index];
            match context.values.get(parameter.name()) {
                Some(ProgramValue::Int32(term)) => Ok(term.clone()),
                _ => Err(ClickError::new(format!(
                    "`{claim_label}` kernel parameter `{}` must be int32",
                    parameter.name()
                ))),
            }
        };
        let value = int32_parameter(0)?;
        match theorem.name() {
            "click::integer::int32_remainder_to_integer" => {
                crate::kernel::prove_int32_remainder_to_integer(value, int32_parameter(1)?)
            }
            "int32_le_antisymmetric" => prove_int32_le_antisymmetric(value, int32_parameter(1)?),
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
    // The declaration lowers each comparison of exact observations to its
    // native form, which states every order as `<` or `<=`; the axiom is
    // compared in that same form.
    let comparable = |proposition: &Proposition| {
        oriented_order_comparisons(&crate::kernel::assumptions::canonical_observation_form(
            proposition,
        ))
    };
    // Native and retained mask/shift comparisons denote the same stated
    // fact. Use the existing exact identity (including types and states),
    // not equality of their temporary carrier representations.
    if !crate::kernel::proof::propositions_are_alpha_equal(
        &comparable(axiom.proposition()),
        &comparable(&expected),
    ) {
        return Err(ClickError::new(format!(
            "`{claim_label}` declaration does not match its kernel axiom",
        )));
    }
    Ok(VerifiedPureTheorem {
        theorem_definition: theorem.clone(),
        ensure_index,
        ensure_clause: ensure_clause.clone(),
        proof_kind: ProofKind::Axiom,
        proof: None,
        contract_value_parameters: None,
        requires: context.requires.clone(),
        conclusion: goal,
        kernel_authority: None,
        checked_completion: None,
    })
}

/// Run source once through the checked operation driver and retain its result.
#[allow(clippy::too_many_arguments)]
fn check_pure_script_with_proof(
    claim_label: &str,
    context: &PureTheoremContext,
    surface_goal: &SyntaxProposition,
    goal: &Proposition,
    goal_introductions: &crate::kernel::LoweringIntroductions,
    entry_requirements: &super::execution_planning::OpenObligationProbe,
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
    let all_sites = claim_script_sites(&root, tactics, 0);
    let prefix = if entry_requirements.recorded.is_empty() {
        0
    } else {
        tactics
            .iter()
            .take_while(|tactic| matches!(tactic, ProofTactic::Have(_)))
            .count()
    };
    let root = if prefix == 0 {
        root
    } else {
        let mut unfinished = None;
        let completed = root.driver().try_addressed_linear_script(
            &tactics[..prefix],
            &all_sites[..prefix],
            &mut None,
            Some(&mut unfinished),
            false,
        )?;
        if completed.is_some() {
            return Err(ClickError::new(
                "theorem entry requirements must be proved before closing the conclusion",
            ));
        }
        unfinished
            .ok_or_else(|| ClickError::new("theorem entry requirement prelude did not complete"))?
    };
    let root = root
        .driver()
        .discharge_entry_requirements(surface_goal, entry_requirements)?;
    let tactics = &tactics[prefix..];
    let mut search = super::attempt::search_scope("pure theorem script");
    let mut declined = None;
    let sites = &all_sites[prefix..];
    let mut unfinished = None;
    let checked = match root.driver().try_addressed_linear_script(
        tactics,
        sites,
        &mut declined,
        Some(&mut unfinished),
        true,
    ) {
        Ok(checked) => checked,
        Err(error) => return Err(error.with_search_failures(search.finish())),
    };
    let Some(proof) = checked else {
        check_verification_deadline()?;
        let detail = match declined {
            Some(super::smart_closures::LinearScriptDecline::Shape) => {
                "contains an unsupported operation or control-flow shape".to_string()
            }
            Some(
                super::smart_closures::LinearScriptDecline::Step(index)
                | super::smart_closures::LinearScriptDecline::UnsuccessfulSearch(index),
            ) => format!(
                "could not complete tactic {} (`{}`)",
                prefix + index + 1,
                tactic_name(&tactics[index])
            ),
            None => "ended with its goal still open".to_string(),
        };
        return Err(unfinished
            .as_ref()
            .unwrap_or(&root)
            .step_error(format!("checked pure script for `{claim_label}` {detail}"))
            .with_proof_refusal(match declined {
                None => crate::surface::ProofRefusal::IncompleteProof,
                Some(super::smart_closures::LinearScriptDecline::UnsuccessfulSearch(_)) => {
                    crate::surface::ProofRefusal::UnsuccessfulSearch
                }
                Some(_) => crate::surface::ProofRefusal::Tactic,
            })
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
    proposition: &SyntaxProposition,
    known_facts: &[SyntaxProposition],
) -> Vec<ClickFunctionApplication> {
    click_function_applications_with(
        proposition,
        &KnownGuards {
            facts: known_facts,
            constants: false,
        },
    )
}

/// The applications of [`click_function_applications`], also entering the arm
/// an `if` over constants selects, such as `if 2 <= 0` in an unfolded
/// recursive body. The arms are only candidates: an `unfold` of an
/// application in either arm is valid, so a guard read here only directs the
/// search.
pub(super) fn click_function_applications_deciding_constant_guards(
    proposition: &SyntaxProposition,
) -> Vec<ClickFunctionApplication> {
    click_function_applications_with(
        proposition,
        &KnownGuards {
            facts: &[],
            constants: true,
        },
    )
}

/// What decides an `if` guard while collecting applications.
struct KnownGuards<'a> {
    facts: &'a [SyntaxProposition],
    /// Also decide a guard that compares constants.
    constants: bool,
}

fn click_function_applications_with(
    proposition: &SyntaxProposition,
    known_facts: &KnownGuards<'_>,
) -> Vec<ClickFunctionApplication> {
    fn fact_polarity(
        proposition: &SyntaxProposition,
        known_facts: &KnownGuards<'_>,
    ) -> Option<bool> {
        if known_facts.facts.contains(proposition) {
            return Some(true);
        }
        let negated = SyntaxProposition::Not(Box::new(proposition.clone()));
        if known_facts.facts.contains(&negated) {
            return Some(false);
        }
        known_facts
            .constants
            .then(|| constant_guard_value(proposition))
            .flatten()
    }

    fn expression(
        term: &SyntaxTerm,
        known_facts: &KnownGuards<'_>,
        applications: &mut Vec<ClickFunctionApplication>,
    ) {
        match term {
            SyntaxTerm::IntegerContext(value) => expression(value, known_facts, applications),

            SyntaxTerm::Proposition(proposition) => {
                proposition_inner(proposition, known_facts, applications)
            }
            SyntaxTerm::Resource(_) => {}
            SyntaxTerm::RegionResult(_)
            | SyntaxTerm::RegionAllocation(_)
            | SyntaxTerm::RegionParameter { .. } => {}
            SyntaxTerm::Lambda { .. } => {}
            SyntaxTerm::Apply {
                function,
                arguments,
            } => {
                expression(function, known_facts, applications);
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
            }

            SyntaxTerm::IntegerLiteral(_) => {}
            SyntaxTerm::CUnary { operand: inner, .. }
            | SyntaxTerm::MemoryLoad { pointer: inner, .. }
            | SyntaxTerm::Negate(inner) => expression(inner, known_facts, applications),
            SyntaxTerm::ResourceField(_)
            | SyntaxTerm::AlgebraicVariable { .. }
            | SyntaxTerm::Binding(_) => {}
            SyntaxTerm::AlgebraicConstructor { arguments, .. } => {
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
            }
            SyntaxTerm::AlgebraicMatch { scrutinee, arms } => {
                expression(scrutinee, known_facts, applications);
                for arm in arms {
                    expression(&arm.body, known_facts, applications);
                }
            }
            SyntaxTerm::SequenceLiteral(elements) => {
                for element in elements {
                    expression(element, known_facts, applications);
                }
            }
            SyntaxTerm::SequenceConcat(left, right) => {
                expression(left, known_facts, applications);
                expression(right, known_facts, applications);
            }
            SyntaxTerm::MethodCall {
                receiver,
                arguments,
                ..
            } => {
                expression(receiver, known_facts, applications);
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
            }
            SyntaxTerm::Call { name, arguments } => {
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
                if matches!(name.as_str(), "to_integer" | "to_int32") {
                    return;
                }
                let application = ClickFunctionApplication {
                    name: name.clone(),
                    arguments: arguments.clone(),
                };
                if !applications.contains(&application) {
                    applications.push(application);
                }
            }
            SyntaxTerm::Field { base, .. }
            | SyntaxTerm::Old(base)
            | SyntaxTerm::Exact(base)
            | SyntaxTerm::At {
                expression: base, ..
            }
            | SyntaxTerm::BitwiseNot(base) => expression(base, known_facts, applications),
            crate::surface::binary_contract_expression!(left, right) => {
                expression(left, known_facts, applications);
                expression(right, known_facts, applications);
            }
            SyntaxTerm::If {
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
            SyntaxTerm::RangeFold {
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
            SyntaxTerm::Let { value, body, .. } => {
                expression(value, known_facts, applications);
                expression(body, known_facts, applications);
            }
            SyntaxTerm::ResourceCount(resource) => {
                if let ResourceClause::Declared { arguments, .. } = resource.as_ref() {
                    for argument in arguments {
                        expression(argument, known_facts, applications);
                    }
                }
            }
            SyntaxTerm::QualifiedC { .. }
            | SyntaxTerm::ProgramExpression(_)
            | SyntaxTerm::ArrayIndex { .. }
            | SyntaxTerm::ProgramBinding(_)
            | SyntaxTerm::ResourceWildcard => {}
        }
    }

    fn proposition_inner(
        proposition: &SyntaxProposition,
        known_facts: &KnownGuards<'_>,
        applications: &mut Vec<ClickFunctionApplication>,
    ) {
        match proposition {
            SyntaxProposition::Value(value) => expression(value, known_facts, applications),
            SyntaxProposition::Comparison { left, right, .. } => {
                expression(left, known_facts, applications);
                expression(right, known_facts, applications);
            }
            SyntaxProposition::FloatClassification {
                expression: value, ..
            } => {
                expression(value, known_facts, applications);
            }
            SyntaxProposition::Defined { expression: value }
            | SyntaxProposition::IsA { pointer: value, .. } => {
                expression(value, known_facts, applications)
            }
            SyntaxProposition::And(left, right)
            | SyntaxProposition::Or(left, right)
            | SyntaxProposition::Implies(left, right) => {
                proposition_inner(left, known_facts, applications);
                proposition_inner(right, known_facts, applications);
            }
            SyntaxProposition::Not(body)
            | SyntaxProposition::At {
                proposition: body, ..
            }
            | SyntaxProposition::ForAll { body, .. }
            | SyntaxProposition::Exists { body, .. } => {
                proposition_inner(body, known_facts, applications)
            }
            SyntaxProposition::RangeAll {
                start, end, body, ..
            }
            | SyntaxProposition::RangeAny {
                start, end, body, ..
            } => {
                expression(start, known_facts, applications);
                expression(end, known_facts, applications);
                proposition_inner(body, known_facts, applications);
            }
            SyntaxProposition::PredicateCall { arguments, .. } => {
                for argument in arguments {
                    expression(argument, known_facts, applications);
                }
            }
            SyntaxProposition::Separate { .. }
            | SyntaxProposition::ResourceViewable { .. }
            | SyntaxProposition::Contains { .. }
            | SyntaxProposition::Loadable { .. } => {}
        }
    }

    let mut applications = Vec::new();
    proposition_inner(proposition, known_facts, &mut applications);
    applications
}

pub(super) fn induction_application_surface_premises(
    setup: &PureInductionSetup,
    argument: &SyntaxTerm,
) -> Result<Vec<SyntaxProposition>, ClickError> {
    let zero = SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0)));
    let current = SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
        (setup.parameter.clone()).into(),
    ));
    let mut premises = vec![
        SyntaxProposition::Comparison {
            left: zero,
            operator: ComparisonOperator::LessEqual,
            right: argument.clone(),
        },
        SyntaxProposition::Comparison {
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
        let mut pending = vec![substituted];
        while let Some(premise) = pending.pop() {
            if let SyntaxProposition::And(left, right) = premise {
                pending.push(*right);
                pending.push(*left);
            } else if !premises.contains(&premise) {
                premises.push(premise);
            }
        }
    }
    Ok(premises)
}

pub(super) fn lower_pure_theorem_proposition(
    theorem_name: &str,
    proposition: &SyntaxProposition,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_opaque_calls(
        theorem_name,
        proposition,
        contract_environment,
        at,
        spec_definitions,
        &BTreeSet::new(),
    )
}

pub(super) fn lower_pure_theorem_proposition_with_integer_values(
    theorem_name: &str,
    proposition: &SyntaxProposition,
    contract_environment: ContractEnvironment<'_>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_with_algebraic_and_integer_values(
        theorem_name,
        proposition,
        contract_environment,
        &BTreeMap::new(),
        integer_values,
        at,
        spec_definitions,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_with_algebraic_and_integer_values(
    theorem_name: &str,
    proposition: &SyntaxProposition,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    lower_pure_theorem_proposition_recording_introductions(
        theorem_name,
        proposition,
        &PureFactContext::new(),
        contract_environment,
        algebraic_values,
        integer_values,
        at,
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
    proposition: &SyntaxProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(Proposition, crate::kernel::LoweringIntroductions), String> {
    lower_pure_theorem_proposition_for_proof(
        theorem_name,
        proposition,
        assumptions,
        contract_environment,
        algebraic_values,
        integer_values,
        at,
        spec_definitions,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_pure_theorem_proposition_for_proof(
    theorem_name: &str,
    proposition: &SyntaxProposition,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
    is_conjunct_label: bool,
) -> Result<(Proposition, crate::kernel::LoweringIntroductions), String> {
    let state = ExecutionState::at_point(at);
    lower_fixed_state_proposition_through_kernel_with_introductions(
        proposition,
        &PureFactContext::new(),
        contract_environment,
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        spec_definitions,
        FixedStateLoweringOptions {
            is_conjunct_label,
            algebraic_values: Some(algebraic_values),
            integer_values: Some(integer_values),
            obligation_assumptions: Some(assumptions),
            ..Default::default()
        },
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

/// A pure theorem's proposition lowered at its parameter state by the
/// kernel, with the calls named in `opaque_click_functions` kept as
/// applications.
fn lower_pure_theorem_proposition_with_opaque_calls(
    theorem_name: &str,
    proposition: &SyntaxProposition,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
    opaque_click_functions: &BTreeSet<String>,
) -> Result<Proposition, String> {
    let state = ExecutionState::at_point(at);
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        &PureFactContext::new(),
        contract_environment,
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
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
    proposition: &SyntaxProposition,
    assumptions: &PureFactContext,
    context: &PureTheoremContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let opaque = spec_definitions
        .functions
        .definitions
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>();
    let state = ExecutionState::at_point(&context.point);
    lower_fixed_state_proposition_through_kernel_with(
        proposition,
        assumptions,
        ContractEnvironment::new(&context.values, &context.array_refs),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        spec_definitions,
        FixedStateLoweringOptions {
            integer_values: Some(&context.integer_values),
            opaque_click_functions: Some(&opaque),
            ..Default::default()
        },
    )
    .map_err(|error| format!("pure theorem `{theorem_name}`: {error}"))
}

/// `proposition` with each order comparison stated as `<` or `<=`: `a > b`
/// as `b < a` and `a >= b` as `b <= a`. A comparison of exact observations
/// lowers to that orientation (`canonical_observation_form`), while a kernel
/// axiom states the order its lemma writes; both name the same fact.
fn oriented_order_comparisons(proposition: &Proposition) -> Proposition {
    use crate::kernel::OldConditionTerm as Condition;
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            let oriented = match condition.old_form() {
                Condition::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left,
                    right,
                } => Condition::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: right.clone(),
                    right: left.clone(),
                },
                Condition::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left,
                    right,
                } => Condition::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: right.clone(),
                    right: left.clone(),
                },
                Condition::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::GreaterThan,
                    left,
                    right,
                } => Condition::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::LessThan,
                    left: right.clone(),
                    right: left.clone(),
                },
                Condition::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::GreaterEqual,
                    left,
                    right,
                } => Condition::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::LessEqual,
                    left: right.clone(),
                    right: left.clone(),
                },
                Condition::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::GreaterThan,
                    left,
                    right,
                } => Condition::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessThan,
                    left: right.clone(),
                    right: left.clone(),
                },
                Condition::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::GreaterEqual,
                    left,
                    right,
                } => Condition::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessEqual,
                    left: right.clone(),
                    right: left.clone(),
                },
                Condition::IntegerGreaterThan(left, right) => {
                    Condition::IntegerLessThan(right.clone(), left.clone())
                }
                Condition::IntegerGreaterEqual(left, right) => {
                    Condition::IntegerLessEqual(right.clone(), left.clone())
                }
                other => other.clone(),
            };
            Proposition::condition_is(oriented, *value)
        }
        Proposition::Not(inner) => Proposition::Not(Box::new(oriented_order_comparisons(inner))),
        Proposition::And(left, right) => Proposition::And(
            Box::new(oriented_order_comparisons(left)),
            Box::new(oriented_order_comparisons(right)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(oriented_order_comparisons(left)),
            Box::new(oriented_order_comparisons(right)),
        ),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(oriented_order_comparisons(left)),
            Box::new(oriented_order_comparisons(right)),
        ),
        other => other.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn theorem_array_parameter_retains_the_theorem_point() {
        let file =
            crate::surface::parse("theorem array_input(a: int32[]) { ensures true; }").unwrap();
        let theorem = &file.theorem_definitions()[0];
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let context =
            pure_theorem_context(theorem, SpecDefinitions::new(&predicates, &functions)).unwrap();
        let array = context
            .array_refs
            .get("a")
            .expect("the theorem array parameter");
        assert!(context.point.id().is_some());
        assert_eq!(array.point.id(), context.point.id());
    }

    #[test]
    fn axiom_comparison_states_each_order_as_less_than_or_less_equal() {
        use crate::kernel::OldConditionTerm as Condition;
        let word = |index| Box::new(OldMachineTerm::Variable(crate::kernel::Variable(index)));
        let fact = |condition| Proposition::condition_is(condition, true);
        let greater = Proposition::Implies(
            Box::new(fact(Condition::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: word(0),
                right: word(1),
            })),
            Box::new(Proposition::Not(Box::new(fact(Condition::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: word(2),
                right: word(3),
            })))),
        );
        let less = Proposition::Implies(
            Box::new(fact(Condition::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: word(1),
                right: word(0),
            })),
            Box::new(Proposition::Not(Box::new(fact(Condition::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: word(3),
                right: word(2),
            })))),
        );
        assert_eq!(oriented_order_comparisons(&greater), less);
        assert_eq!(oriented_order_comparisons(&less), less);
        // Orientation swaps operands; it does not reverse the order.
        let reversed = fact(Condition::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: word(0),
            right: word(1),
        });
        assert_ne!(
            oriented_order_comparisons(&fact(Condition::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: word(0),
                right: word(1)
            })),
            reversed
        );
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 1.3s in the parallel gate"]
    fn pure_requirements_use_earlier_evaluation_guards_without_dropping_them() {
        for (parameters, arguments, expression, wrong_expression) in [
            ("n: int32", "n", "n + 1", "n - 1"),
            ("n: int64", "n", "n + 1i64", "n - 1i64"),
            // Unsigned division is total; signed division still owes
            // `n != MIN or d != -1`.
            ("n: int32, d: int32", "n, d", "n / d", "n + d"),
            ("n: int64, d: int64", "n, d", "n / d", "n + d"),
        ] {
            let guard = format!("requires defined({expression});");
            let observation = format!("requires to_integer({expression}) == 1;");
            let source = format!(
                "theorem guarded({parameters}) {{ {guard} {observation} ensures to_integer({expression}) == 1 by {{ close(); }} }}"
            );
            crate::surface::verify_c_sources(&source, &[]).unwrap();
            let expanded =
                crate::surface::expand_c_claim_source_by_label(&source, &[], "guarded.ensures_0")
                    .unwrap();
            crate::surface::verify_c_sources(&expanded, &[]).unwrap();
            for invalid in [
                source.replace(&guard, ""),
                source.replace(&guard, &format!("requires defined({wrong_expression});")),
                source.replace(
                    &format!("{guard} {observation}"),
                    &format!("{observation} {guard}"),
                ),
            ] {
                assert!(
                    crate::surface::verify_c_sources(&invalid, &[]).is_err(),
                    "{invalid}"
                );
            }
            let caller = format!(
                "{source} theorem caller({parameters}) {{ {guard} {observation} ensures to_integer({expression}) == 1 by {{ apply(guarded({arguments})); close(); }} }}"
            );
            crate::surface::verify_c_sources(&caller, &[]).unwrap();
        }
        let source = "theorem byte_at_next(bytes: uint8[], n: int32, value: Integer) { requires defined(n + 1); requires value == to_integer(bytes[n + 1] as int32); ensures value == to_integer(bytes[n + 1] as int32) by { close(); } }";
        crate::surface::verify_c_sources(source, &[]).unwrap();
        assert!(
            crate::surface::verify_c_sources(&source.replace("requires defined(n + 1);", ""), &[])
                .is_err()
        );
        let missing_call_guard = "theorem guarded(n: int32) { requires defined(n + 1); requires to_integer(n + 1) == 1; ensures n == n by { close(); } } theorem caller(n: int32) { ensures n == n by { apply(guarded(n)); close(); } }";
        assert!(crate::surface::verify_c_sources(missing_call_guard, &[]).is_err());
    }

    #[test]
    fn ordinary_pure_scripts_retain_completion_without_compatibility() {
        for body in [
            "close();",
            "have x == x by { close(); } close();",
            "if x == 0 { close(); } else { close(); }",
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
            "theorem bad(x: int32) { ensures x == 0 by { close() using {}; close(); } }",
        )
        .unwrap_err();
        assert!(
            error.message().contains("`close() using` could not prove"),
            "{}",
            error.message()
        );
        let error = verify_instantiation_theorem(
            "theorem unsupported() { ensures 0 == 0 by { step_until(function.exit); } }",
        )
        .unwrap_err();
        assert!(
            error.message().contains("step_until"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn ordinary_pure_fact_producers_preserve_written_suffixes() {
        let source = r#"
            theorem identity(x: int32) { requires x == 0; ensures x == 0 by { close(); } }
            theorem application(x: int32) {
                requires x == 0;
                ensures x == 0 by { apply(identity(x)); rewrite(x, 0); close(); }
            }
            theorem extraction(x: int32) {
                requires x == 0 and x <= 1;
                ensures x == 0 by { have x == 0 by close(); rewrite(x, 0); close(); }
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
                crate::surface::expand_c_claim_source_by_label(source, &[], label).unwrap();
            crate::surface::verify_c_sources(&expanded, &[]).unwrap();
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 1.0s in the parallel gate"]
    fn ordinary_pure_numeric_induction_expands_and_reverifies() {
        let library = TheoremEnvironment::with_standard_library(&[]).unwrap();
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
            let result = verify_instantiation_theorem_in_environment(source, &library);
            let verified = result.unwrap();
            assert!(matches!(
                verified.checked_completion,
                Some(TheoremProofCompletion::Proposition(_))
            ));
            assert!(verified.kernel_authority.is_some());
            let label = format!("{}.ensures_0", verified.theorem_definition.name());
            crate::surface::verify_c_sources(source, &[]).unwrap();
            let expanded =
                crate::surface::expand_c_claim_source_by_label(source, &[], &label).unwrap();
            crate::surface::verify_c_sources(&expanded, &[]).unwrap();
            assert_eq!(
                expanded,
                crate::surface::expand_c_claim_source_by_label(&expanded, &[], &label).unwrap()
            );
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: induction prefix scope and cold expansion replay"]
    fn scalar_induction_prefixes_preserve_scope_and_cold_replay() {
        let fixture = include_str!("../../../mdtests/scalar_induction_after_helper_facts.md");
        let source = fixture
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        let global_before_local = format!(
            "theorem ih(n: int32) {{ ensures n == n by close(); }}\n{}",
            source.replace("have n == n;", "have n == n by { apply(ih(n)); }")
        );
        for source in [source.to_string(), global_before_local] {
            crate::surface::verify_c_sources(&source, &[]).unwrap();
            let expanded = crate::surface::expand_c_claim_source_by_label(
                &source,
                &[],
                "countdown_is_zero.ensures_0",
            )
            .unwrap();
            crate::surface::proof::without_implicit_solve(|| {
                crate::surface::verify_c_sources(&expanded, &[])
            })
            .unwrap();
        }
        crate::surface::verify_c_sources(
            "theorem unsigned_prefix(n: uint64) { ensures n == n by { have 0u64 <= n; let ih = induct(n); close(); } }", &[],
        ).unwrap();
        for (invalid, diagnostic) in [
            (
                source.replace(
                    "have n == n;",
                    "have n == n by { if n > 0 { apply(ih(0)); close(); } else { close(); } }",
                ),
                "ih",
            ),
            (
                source.replace(
                    "let ih = induct(n);",
                    "let ih = induct(n); let another = induct(n);",
                ),
                "only one top-level",
            ),
            (
                source.replace(
                    "have n == n;",
                    "have n == n by { let ih = induct(n); close(); }",
                ),
                "only one top-level",
            ),
        ] {
            let error = crate::surface::verify_c_sources(&invalid, &[])
                .expect_err("invalid induction scope must be refused");
            assert!(error.message().contains(diagnostic), "{}", error.report());
            assert!(!error.message().contains("budget"), "{}", error.report());
        }
        let changed_goal = "theorem changed_goal(n: int32) { requires n >= 0; ensures n >= 0 implies n >= 0 by { intro() { let ih = induct(n); close(); } } }";
        let error = crate::surface::verify_c_sources(changed_goal, &[])
            .expect_err("a subproof cannot introduce its own induction goal");
        assert!(
            error
                .message()
                .contains("only one top-level `induct` tactic"),
            "{}",
            error.report()
        );
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 9.1s in the parallel gate"]
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
        crate::surface::verify_c_sources(source, &[]).unwrap();
        let expanded =
            crate::surface::expand_c_claim_source_by_label(source, &[], "guarded_count.ensures_0")
                .unwrap();
        crate::surface::verify_c_sources(&expanded, &[]).unwrap();
        let missing_evidence = source
            .lines()
            .filter(|line| {
                !line.contains("have n - 1 <= 1000000")
                    && !line.contains("have to_integer(n - 1) <= 1000000")
            })
            .collect::<Vec<_>>()
            .join("\n");
        let label = "guarded_count.ensures_0";
        let refusal = crate::surface::without_implicit_solve_for_claim(label, || {
            crate::surface::verify_c_sources(&missing_evidence, &[]).map_err(|error| error.report())
        })
        .expect_err("cold replay needs the bound on the induction argument");
        assert!(refusal.contains("1000000"), "{refusal}");

        let expanded =
            crate::surface::expand_c_claim_source_by_label(&missing_evidence, &[], label).unwrap();
        crate::surface::without_implicit_solve_for_claim(label, || {
            crate::surface::verify_c_sources(&expanded, &[]).map_err(|error| error.report())
        })
        .unwrap();
        let false_claim = source.replace(
            "ensures guarded_countdown(n) == 0 and",
            "ensures guarded_countdown(n) == 1 and",
        );
        assert!(crate::surface::verify_c_sources(&false_claim, &[]).is_err());
    }

    #[test]
    fn structural_induction_declaration_requires_its_matching_cases() {
        let source = r#"
            spec enum Chain { Nil, Link(Chain), }
            theorem reflexive(xs: Chain, ys: Chain) {
                ensures xs == xs by {
                    let ih = induct(xs);
                    match xs {
                        Chain::Nil => { close(); }
                        Chain::Link(tail) => { apply(ih(tail)); close(); }
                    }
                }
            }
        "#;
        let verified = verify_instantiation_theorem(source).unwrap();
        assert!(matches!(verified.proof_certificate().unwrap().steps(),
            [ProofStep::Induct { .. }, ProofStep::Match { arms, .. }] if arms.len() == 2));
        for (bad, diagnostic) in [
            (
                source.replace("match xs", "match ys"),
                "immediate recursive field",
            ),
            (
                source.replace("match xs {", "match xs ensuring { fact xs == xs; } {"),
                "does not take `ensuring`",
            ),
            (
                source.replace("apply(ih(tail));", "let inner = induct(tail);"),
                "same theorem parameter",
            ),
            (
                source.replace("apply(ih(tail));", "apply(ih(xs));"),
                "immediate recursive field",
            ),
        ] {
            let error =
                verify_instantiation_theorem(&bad).expect_err("invalid induction must fail");
            assert!(error.report().contains(diagnostic), "{}", error.report());
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: structural induction scope, expansion, and cold replay matrix"]
    fn structural_induction_surrounding_helpers_expand_and_cold_replay() {
        let source = include_str!("../../../mdtests/structural_induction_surrounding_helpers.md")
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        crate::surface::verify_c_sources(source, &[]).unwrap();
        for theorem in [
            "surrounding",
            "match_in_helper",
            "branch_before_declaration",
            "branch_after_declaration",
        ] {
            let expanded = crate::surface::expand_c_claim_source_by_label(
                source,
                &[],
                &format!("{theorem}.ensures_0"),
            )
            .unwrap();
            crate::surface::without_implicit_solve(|| {
                crate::surface::verify_c_sources(&expanded, &[])
            })
            .unwrap();
        }
        let false_source = source.replace(
            "Chain::Link(tail) => Chain::Link(copy_chain(tail))",
            "Chain::Link(tail) => Chain::Nil",
        );
        assert!(crate::surface::verify_c_sources(&false_source, &[]).is_err());
        let premature = source.replace(
            "have before: n >= 0 by close();",
            "have before: n >= 0 by { apply(ih(xs)); }",
        );
        assert!(crate::surface::verify_c_sources(&premature, &[]).is_err());
        let continuation = include_str!("../../../mdtests/structural_induction_continuation.md")
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        let census = crate::surface::proof::raise_lower_census::capture(|| {
            crate::surface::verify_c_sources(continuation, &[]).unwrap();
        });
        assert!(
            census.iter().all(|line| line.starts_with("raised\t")),
            "{census:#?}"
        );
        let expanded = crate::surface::expand_c_claim_source_by_label(
            continuation,
            &[],
            "continuation.ensures_0",
        )
        .unwrap();
        crate::surface::without_implicit_solve(|| crate::surface::verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.report()));
        let dangling =
            continuation.replace("have xs == xs by close();", "have tail == tail by close();");
        assert!(
            crate::surface::verify_c_sources(&dangling, &[]).is_err(),
            "match fields remain arm-local"
        );
    }

    #[test]
    fn ordinary_pure_structural_induction_retains_arm_evidence() {
        let source = r#"
            spec enum TestNat { Zero, Succ(TestNat), }
            theorem reflexive(n: TestNat) {
                ensures n == n by {
                    let ih = induct(n);
                    match n {
                        TestNat::Zero => { close(); }
                        TestNat::Succ(tail) => { close(); }
                    }
                }
            }
        "#;
        let verified = crate::surface::verify_click_theorems(source)
            .unwrap()
            .remove(0);
        assert!(verified.kernel_authority.is_none());
        assert!(matches!(
            &verified.checked_completion,
            Some(TheoremProofCompletion::Proposition(_))
        ));
        assert!(
            matches!(verified.proof_certificate().unwrap().steps(), [ProofStep::Induct { .. }, ProofStep::Match { arms, .. }] if arms.len() == 2)
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
                }, x);
                close();
            }
        }
    "#;

    fn verify_instantiation_theorem(source: &str) -> Result<VerifiedPureTheorem, ClickError> {
        verify_instantiation_theorem_in_environment(source, &TheoremEnvironment::new(&[]))
    }

    fn verify_instantiation_theorem_in_environment(
        source: &str,
        theorems: &TheoremEnvironment,
    ) -> Result<VerifiedPureTheorem, ClickError> {
        let file = crate::surface::parse(source)?;
        let predicates = PredicateEnvironment::new(file.predicate_definitions());
        let functions = ClickFunctionEnvironment::with_algebraic_types(
            file.click_function_definitions(),
            file.algebraic_type_definitions(),
        );
        let mut verified = verify_concrete_theorem_definition(
            &file.theorem_definitions()[0],
            SpecDefinitions::new(&predicates, &functions),
            theorems,
            None,
        )?;
        Ok(verified.remove(0))
    }

    #[test]
    fn multi_argument_instantiation_checks_all_values_and_replays() {
        let quantified =
            "forall (i: int32) { forall (j: uint64) { to_integer(i) <= to_integer(j) } }";
        let intermediate = "forall (j: uint64) { to_integer(x) <= to_integer(j) }";
        let theorem = |goal: &str, arguments: &str| {
            format!(
                "theorem inst(x: int32) {{ requires {quantified}; ensures {goal} by {{ instantiate({quantified}, {arguments}); close(); }} }}"
            )
        };
        for (goal, arguments) in [
            ("to_integer(x) <= 7", "x, 7u64"),
            (intermediate, "x, 7u64"),
            (intermediate, "x"),
        ] {
            let source = theorem(goal, arguments);
            let verified = verify_instantiation_theorem(&source)
                .unwrap_or_else(|error| panic!("{}", error.report()));
            let certificate = format_proof_certificate(verified.proof.as_ref().unwrap());
            assert!(
                certificate.contains(&format!(", {arguments});")),
                "{certificate}"
            );
            let (head, _) = source.split_once(" by {").unwrap();
            let replay = format!("{head} {certificate} }}");
            crate::surface::without_implicit_solve(|| verify_instantiation_theorem(&replay))
                .unwrap_or_else(|error| panic!("{}\n{replay}", error.report()));
        }
        let wrong_type = theorem(intermediate, "x, x");
        let error = verify_instantiation_theorem(&wrong_type).unwrap_err();
        assert!(
            error.message().contains("did not evaluate to uint64"),
            "{error}"
        );
        let too_many = theorem(intermediate, "x, 7u64, 0");
        let error = verify_instantiation_theorem(&too_many).unwrap_err();
        assert!(
            error
                .message()
                .contains("argument 3 has no remaining universal binder"),
            "{error}"
        );
    }

    #[test]
    fn pure_instantiate_retains_checked_authority_without_recertification() {
        let result = verify_instantiation_theorem(INSTANTIATE_BOUND);
        let verified = result.expect("pure instantiation must produce checked authority");
        assert!(verified.kernel_authority.is_some());
        assert!(matches!(
            verified.proof.as_ref().unwrap().steps(),
            [ProofStep::Instantiate { .. }, ProofStep::Known]
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
        let expanded =
            crate::surface::expand_c_claim_source_by_label(source, &[], "obtained_int32.ensures_0")
                .unwrap();
        crate::surface::verify_c_sources(&expanded, &[]).unwrap();
    }

    #[test]
    fn pure_instantiate_preserves_a_missing_guard_until_known() {
        let missing = INSTANTIATE_BOUND.replace("requires x < limit;", "");
        let error = verify_instantiation_theorem(&missing)
            .expect_err("the guarded conclusion needs its missing bound");
        assert!(
            error.message().contains("`known` requires"),
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
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn pure_instantiate_preserves_an_unrelated_open_goal() {
        let open = INSTANTIATE_BOUND
            .replace("ensures x <= upper", "ensures x == upper")
            .replace("                close();", "");
        let error = verify_instantiation_theorem(&open)
            .expect_err("instantiation does not change the selected goal");
        assert!(
            error.proof_refusal() == Some(crate::surface::ProofRefusal::UnsuccessfulSearch),
            "{}",
            error.message()
        );
        let failed = INSTANTIATE_BOUND.replace("ensures x <= upper", "ensures x == upper");
        let error = verify_instantiation_theorem(&failed)
            .expect_err("the explicit closer must fail on the original goal");
        assert!(error.message().contains("known"), "{}", error.message());
        assert!(
            !error.message().contains("round-trip"),
            "{}",
            error.message()
        );
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn pure_instantiate_resolves_introduced_binders_and_nested_shadowing() {
        let source = r#"
            theorem shadowed(x: int32) {
                requires x == 0;
                requires forall (k: int32) { k <= 10 implies k <= 20 };
                ensures forall (x: int32) { x <= 10 implies x <= 20 } by {
                    intro() {
                        intro() {
                            have x <= 20 by {
                                instantiate(forall (x: int32) { x <= 10 implies x <= 20 }, x);
                                close();
                            }
                            close();
                        }
                    }
                }
            }
        "#;
        let verified = verify_instantiation_theorem(source)
            .expect("intro bindings must shadow theorem parameters");
        assert!(verified.kernel_authority.is_some());
        let invalid = source.replace("have x <= 20 by {", "have x == 0 by {");
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
                    instantiate(forall (k: int32) { forall (k: int32) { k == k } }, 0);
                    close();
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
            "ensures x <= upper by { let ih = induct(x);",
        );
        let source = source.replace(
            "instantiate(forall",
            "have 0 <= x by close(); instantiate(forall",
        );
        let verified = verify_instantiation_theorem(&source);
        assert!(verified.unwrap().kernel_authority.is_some());
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.5s in the parallel gate"]
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
                &context.point,
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
            let tactics = theorem.ensures()[0].proof().tactics().unwrap();
            let certificate = ProofCertificate::from_proof_tactics(&tactics[..1]).unwrap();
            let before = crate::persistent::persistent_node_allocations();
            let instantiated = root
                .driver()
                .apply_step(certificate.steps()[0].clone())
                .unwrap();
            allocations.push(crate::persistent::persistent_node_allocations() - before);
            // Instantiation retains the guarded body; propagation exposes the
            // consequence and an explicit known closes it.
            assert!(!instantiated.is_complete());
            assert!(instantiated.facts().pure_known_available(&goal));
            assert!(root.certificate().steps().is_empty());
            assert!(!root.facts().contains(&goal));
            instantiated
                .driver()
                .apply_step(ProofStep::Known)
                .unwrap()
                .completed_proposition()
                .unwrap();
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
        crate::surface::verify_c_sources(source, &[]).unwrap();
        let expanded = crate::surface::expand_c_claim_source_by_label(
            source,
            &[],
            "instantiate_bound_caller.ensures_0",
        )
        .unwrap();
        assert_ne!(source, expanded);
        crate::surface::verify_c_sources(&expanded, &[]).unwrap();
        let repeated = crate::surface::expand_c_claim_source_by_label(
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
                    intro() {
                        instantiate(forall (k: int32) { k == k }, x);
                        close();
                    }
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
            theorem branched(x: int32, flag: int32) {
                requires forall (k: int32) { k <= 0 };
                requires flag == 0 or flag != 0;
                ensures x <= 0 by {
                    if flag == 0 {
                        instantiate(forall (k: int32) { k <= 0 }, x);
                        close();
                    } else {
                        instantiate(forall (k: int32) { k <= 0 }, x);
                        close();
                    }
                    close();
                }
            }
        "#;
        let cases = source
            .replace("if flag == 0 {", "cases {\n flag == 0 => {")
            .replace("} else {", "}\n flag != 0 => {")
            .replace(
                "                    }\n                    close();",
                "                    }\n }\n                    close();",
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
                assert!(matches!(arm.steps(), [ProofStep::Instantiate { .. }]));
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
            let wrong_sibling =
                source.replacen("instantiate(forall (k: int32) { k <= 0 }, x);", "", 1);
            let error = verify_instantiation_theorem(&wrong_sibling).unwrap_err();
            assert!(error.message().contains("known"), "{}", error.message());
        }
    }

    fn verify_standard_declaration(source: &str) -> Result<(), ClickError> {
        verify_standard_declarations(source).map(|_| ())
    }

    fn verify_standard_declarations(source: &str) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
        let mut file = crate::surface::parser::parse_library_file_items(source)?;
        // The kernel checks a library theorem by its qualified identity, so
        // the test declaration is named as the library names it.
        for theorem in &mut file.theorem_definitions {
            theorem.name = crate::surface::names::library_theorem_identity(&theorem.name);
        }
        let predicate_environment = PredicateEnvironment::new(file.predicate_definitions())
            .with_contracts(file.contract_definitions(), &file.program_function_names);
        let click_function_environment =
            ClickFunctionEnvironment::new(file.click_function_definitions());
        let spec_definitions =
            SpecDefinitions::new(&predicate_environment, &click_function_environment);
        let theorem = file
            .theorem_definitions()
            .first()
            .ok_or_else(|| ClickError::new("test source did not contain a theorem"))?;
        verify_theorem_definition(
            theorem,
            spec_definitions,
            &TheoremEnvironment::new(&[]),
            None,
        )
    }

    /// A C index has no rigid type, so the generic element law's own entry
    /// point checks it at each index type its kernel builder admits rather
    /// than refusing the rigid index.
    #[test]
    fn generic_element_containment_law_keeps_its_bounds_and_exclusive_end() {
        let source = "theorem click::separation::contains_element<T, I>(p: T*, lo: I, hi: I, i: I) { requires lo <= i; requires i < hi; ensures contains(memory(p[lo..hi]), memory(p[i])); }";
        assert_eq!(verify_standard_declarations(source).unwrap().len(), 2);
        for invalid in [
            source.replace("requires lo <= i;", ""),
            source.replace("i < hi", "i <= hi"),
            source.replace("memory(p[i])", "memory(p[hi])"),
        ] {
            assert!(verify_standard_declarations(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn generic_element_separation_law_is_checked_at_each_admitted_index_type() {
        let source = "theorem click::separation::separate_elements<T, I>(p: T*, i: I, j: I) { requires i != j; ensures separate(memory(p[i]), memory(p[j])); }";
        let verified = verify_standard_declarations(source).expect("element separation law");
        assert_eq!(verified.len(), 3);
        assert!(verified.iter().all(|result| {
            result.theorem_definition.name() == "click::separation::separate_elements"
                && result.ensure_index == 0
        }));
        for invalid in [
            source.replace("requires i != j;", ""),
            source.replace("memory(p[j])", "memory(p[i])"),
        ] {
            assert!(verify_standard_declarations(&invalid).is_err(), "{invalid}");
        }
    }

    /// The element-address law is checked like the element law: at each
    /// admitted index type, against its kernel builder's proposition.
    #[test]
    fn generic_element_address_law_is_checked_at_each_admitted_index_type() {
        let source = "theorem click::separation::distinct_elements<T, I>(p: T*, i: I, j: I) { requires i != j; ensures &p[i] != &p[j]; }";
        let verified = verify_standard_declarations(source).expect("element address law");
        assert_eq!(verified.len(), 3);
        assert!(verified.iter().all(|result| {
            result.theorem_definition.name() == "click::separation::distinct_elements"
                && result.ensure_index == 0
        }));
        for invalid in [
            source.replace("requires i != j;", ""),
            source.replace("&p[j]", "&p[i]"),
            source.replace("&p[i] != &p[j]", "&p[i] == &p[j]"),
        ] {
            assert!(verify_standard_declarations(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn divisor_sign_declarations_check_their_guards_and_conclusions() {
        for (name, goal, wrong) in [
            (
                "quotient_negate_divisor",
                "truncating_quotient(n,d) == -truncating_quotient(n,-d)",
                "truncating_quotient(n,d) == truncating_quotient(n,-d)",
            ),
            (
                "remainder_negate_divisor",
                "truncating_remainder(n,d) == truncating_remainder(n,-d)",
                "truncating_remainder(n,d) == -truncating_remainder(n,-d)",
            ),
        ] {
            let source = format!(
                "theorem click::integer::{name}(n: Integer, d: Integer) {{ requires d != 0; requires -d != 0; ensures {goal}; }}"
            );
            verify_standard_declaration(&source).unwrap();
            for bad in [
                source.replace("requires d != 0;", ""),
                source.replace("d != 0", "d == 0"),
                source.replace(goal, wrong),
            ] {
                assert!(verify_standard_declaration(&bad).is_err(), "{bad}");
            }
        }
    }

    #[test]
    fn uint32_byte_representation_declaration_checks_its_target_reads_and_order() {
        let source = include_str!("../../../library/integer.click")
            .split("// Representation bytes")
            .nth(1)
            .unwrap()
            .split_once('\n')
            .unwrap()
            .1
            .split("\ntheorem ")
            .next()
            .unwrap();
        verify_standard_declaration(source).expect("representation declaration");
        for invalid in [
            source.replace("requires little_endian();", ""),
            source.replace("views p[0..1];", ""),
            source.replace("requires defined(p[0]);", ""),
            source.replace("<< 24u32", "<< 16u32"),
            source.replace("[3] as uint32", "[2] as uint32"),
            source.replace("p: uint32*", "p: int32*"),
        ] {
            assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
        }
    }

    #[test]
    fn uint32_division_bridge_declarations_reject_forged_domains_types_and_goals() {
        for (name, op, mathematical) in [
            (
                "click::integer::uint32_divide_to_integer",
                "/",
                "truncating_quotient",
            ),
            (
                "click::integer::uint32_remainder_to_integer",
                "%",
                "truncating_remainder",
            ),
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
                "click::integer::uint64_divide_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right))",
            ),
            (
                "click::integer::uint64_remainder_to_integer",
                "right != 0u64; requires to_integer(right) != 0",
                "to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right))",
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
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn unsigned_unpacking_declarations_require_exact_bounds_words_and_unsigned_shift() {
        for (ty, suffix, packed) in [
            ("uint32", "u32", "(high << 16) | low"),
            ("uint64", "u64", "low | (high << 16)"),
        ] {
            for (name, extraction, result) in [
                ("low", &format!("(({packed}) & 65535{suffix})"), "low"),
                (
                    "high",
                    &format!("((({packed}) >> 16) & 65535{suffix})"),
                    "high",
                ),
            ] {
                let source = format!(
                    "theorem {ty}_unpack_uint16_{name}(low: {ty}, high: {ty}) {{ requires low <= 65535{suffix}; requires high <= 65535{suffix}; ensures {extraction} == {result}; }}"
                );
                verify_standard_declaration(&source).unwrap();
                for invalid in [
                    source.replace(&format!("requires low <= 65535{suffix};"), ""),
                    source.replace(&format!("requires high <= 65535{suffix};"), ""),
                    source.replace("65535", "65536"),
                    source.replace("high << 16", "high << 15"),
                    source.replace(&format!("& 65535{suffix}"), &format!("& 32767{suffix}")),
                    source.replace(&format!("== {result};"), &format!("== 0{suffix};")),
                    source.replace(&format!(": {ty}"), ": int32"),
                    source.replace(
                        &format!(": {ty}"),
                        if ty == "uint32" {
                            ": uint64"
                        } else {
                            ": uint32"
                        },
                    ),
                ] {
                    assert_ne!(source, invalid);
                    assert!(verify_standard_declaration(&invalid).is_err(), "{invalid}");
                }
                if name == "high" {
                    assert!(
                        verify_standard_declaration(&source.replace(">> 16", ">> 15")).is_err()
                    );
                }
            }
        }
    }
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.5s in the parallel gate"]
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
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.9s in the parallel gate"]
    fn integer_truncation_declarations_reject_forged_guards_operands_and_types() {
        for (name, requirements, goal) in [
            (
                "click::integer::truncation_identity",
                &["d != 0"][..],
                "n == truncating_quotient(n, d) * d + truncating_remainder(n, d)",
            ),
            (
                "click::integer::positive_divisor_remainder_lower",
                &["d != 0", "0 < d"][..],
                "1 - d <= truncating_remainder(n, d)",
            ),
            (
                "click::integer::positive_divisor_remainder_upper",
                &["d != 0", "0 < d"][..],
                "truncating_remainder(n, d) <= d - 1",
            ),
            (
                "click::integer::nonnegative_dividend_remainder",
                &["d != 0", "0 <= n"][..],
                "0 <= truncating_remainder(n, d)",
            ),
            (
                "click::integer::nonpositive_dividend_remainder",
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
    mod scaling_tests {
        include!("../../scaling_tests/surface/proof/pure_theorems/tests.rs");
    }
}

#[cfg(test)]
mod function_candidate_tests {
    use super::*;

    #[test]
    fn unfolding_candidates_descend_through_integer_conversions() {
        let call = SyntaxTerm::Call {
            name: "count".into(),
            arguments: vec![],
        };
        let goal = SyntaxProposition::Defined {
            expression: SyntaxTerm::Call {
                name: "to_integer".into(),
                arguments: vec![call],
            },
        };
        let applications = click_function_applications(&goal, &[]);
        assert_eq!(applications.len(), 1);
        assert_eq!(applications[0].name, "count");
    }
}

/// The value of a guard that compares constants, or `None`. A constant is an
/// integer literal or a machine integer constant, through casts, `+`, `-` and
/// negation; any step that leaves its type's range, or a comparison of a
/// signed with an unsigned value, is left undecided.
fn constant_guard_value(proposition: &SyntaxProposition) -> Option<bool> {
    match proposition {
        SyntaxProposition::Not(body) => constant_guard_value(body).map(|value| !value),
        SyntaxProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let (left, left_type) = constant_integer(left)?;
            let (right, right_type) = constant_integer(right)?;
            match (left_type, right_type) {
                (Some(left), Some(right)) if left.is_signed() != right.is_signed() => return None,
                (Some(ty), None) | (None, Some(ty))
                    if !ty.contains(left) || !ty.contains(right) =>
                {
                    return None;
                }
                _ => {}
            }
            Some(match operator {
                ComparisonOperator::Equal => left == right,
                ComparisonOperator::NotEqual => left != right,
                ComparisonOperator::LessThan => left < right,
                ComparisonOperator::LessEqual => left <= right,
                ComparisonOperator::GreaterThan => left > right,
                ComparisonOperator::GreaterEqual => left >= right,
                ComparisonOperator::In => return None,
            })
        }
        _ => None,
    }
}

/// The machine integer types a constant guard reads.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ConstantType {
    Int8,
    UInt8,
    Int32,
    UInt32,
    Int64,
    UInt64,
}

impl ConstantType {
    fn of(program_type: ProgramType) -> Option<Self> {
        Some(match program_type {
            ProgramType::Int8 => Self::Int8,
            ProgramType::UInt8 => Self::UInt8,
            ProgramType::Int32 => Self::Int32,
            ProgramType::UInt32 => Self::UInt32,
            ProgramType::Int64 => Self::Int64,
            ProgramType::UInt64 => Self::UInt64,
            _ => return None,
        })
    }

    fn is_signed(self) -> bool {
        matches!(self, Self::Int8 | Self::Int32 | Self::Int64)
    }

    fn contains(self, value: i128) -> bool {
        match self {
            Self::Int8 => i128::from(i8::MIN) <= value && value <= i128::from(i8::MAX),
            Self::UInt8 => 0 <= value && value <= i128::from(u8::MAX),
            Self::Int32 => i128::from(i32::MIN) <= value && value <= i128::from(i32::MAX),
            Self::UInt32 => 0 <= value && value <= i128::from(u32::MAX),
            Self::Int64 => i128::from(i64::MIN) <= value && value <= i128::from(i64::MAX),
            Self::UInt64 => 0 <= value && value <= i128::from(u64::MAX),
        }
    }
}

/// A constant integer expression's value and machine type, `None` for an
/// `Integer` literal.
fn constant_integer(expression: &SyntaxTerm) -> Option<(i128, Option<ConstantType>)> {
    let in_range = |value: i128, ty: Option<ConstantType>| {
        ty.is_none_or(|ty| ty.contains(value))
            .then_some((value, ty))
    };
    match expression {
        SyntaxTerm::IntegerLiteral(text) => Some((text.parse().ok()?, None)),
        SyntaxTerm::IntegerContext(inner) => constant_integer(inner),
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(value)) => {
            let ty = ConstantType::of(value.program_type())?;
            let value = MachineIntegerType::from_program_type(value.program_type())?
                .constant_from_value(value)?
                .to_i128()?;
            Some((value, Some(ty)))
        }
        // A string literal is read-only, so its byte at a constant index is
        // a constant: `"hi"[1u64]` is `105u8`.
        SyntaxTerm::Index(base, index) => {
            let mut base = base.as_ref();
            while let SyntaxTerm::At { expression, .. } = base {
                base = expression;
            }
            let SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
                pointer,
            ))) = base
            else {
                return None;
            };
            let signed = match pointer.program_type() {
                ProgramType::UInt8Pointer => false,
                ProgramType::Int8Pointer => true,
                _ => return None,
            };
            let address = pointer.address();
            let crate::kernel::AddressBase::StringLiteral { bytes, .. } = &address.base else {
                return None;
            };
            let crate::kernel::OffsetView::Constant(offset) =
                crate::kernel::OffsetTree::view(&address.offset)
            else {
                return None;
            };
            let (index, _) = constant_integer(index)?;
            let byte = *bytes.get(usize::try_from(i128::from(offset) + index).ok()?)?;
            Some(if signed {
                (i128::from(byte as i8), Some(ConstantType::Int8))
            } else {
                (i128::from(byte), Some(ConstantType::UInt8))
            })
        }
        SyntaxTerm::CUnary {
            operand,
            lowered: ProgramExpression::Cast { target_type, .. },
        } => {
            let (value, _) = constant_integer(operand)?;
            in_range(value, Some(ConstantType::of(*target_type)?))
        }
        SyntaxTerm::Negate(inner) => {
            let (value, ty) = constant_integer(inner)?;
            in_range(-value, ty)
        }
        SyntaxTerm::Add(left, right) | SyntaxTerm::Subtract(left, right) => {
            let (left_value, left_type) = constant_integer(left)?;
            let (right_value, right_type) = constant_integer(right)?;
            let ty = match (left_type, right_type) {
                (Some(left), Some(right)) if left != right => return None,
                (left, right) => left.or(right),
            };
            let value = if matches!(expression, SyntaxTerm::Add(..)) {
                left_value + right_value
            } else {
                left_value - right_value
            };
            in_range(value, ty)
        }
        _ => None,
    }
}

/// The program point at which `proposition` names `application`, when a
/// postcondition spells it at the call's entry:
/// `at(region(1).entry, statement(0).call(fprintf, 0).result)
/// == at(region(1).entry, format_length(..))`. The call's array arguments
/// are read at that point, so its value is a different term elsewhere.
pub(super) fn application_point(
    proposition: &SyntaxProposition,
    application: &ClickFunctionApplication,
) -> Option<ProgramPointSelector> {
    fn in_expression(
        term: &SyntaxTerm,
        application: &ClickFunctionApplication,
    ) -> Option<ProgramPointSelector> {
        match term {
            SyntaxTerm::At {
                selector,
                expression,
            } => match expression.as_ref() {
                SyntaxTerm::Call { name, arguments }
                    if *name == application.name && *arguments == application.arguments =>
                {
                    Some(selector.clone())
                }
                inner => in_expression(inner, application),
            },
            SyntaxTerm::AlgebraicConstructor { arguments, .. }
            | SyntaxTerm::Call { arguments, .. } => arguments
                .iter()
                .find_map(|argument| in_expression(argument, application)),
            SyntaxTerm::Proposition(proposition) => application_point(proposition, application),
            _ => None,
        }
    }
    match proposition {
        SyntaxProposition::Value(value) => in_expression(value, application),
        SyntaxProposition::Comparison { left, right, .. } => {
            in_expression(left, application).or_else(|| in_expression(right, application))
        }
        SyntaxProposition::And(left, right) | SyntaxProposition::Or(left, right) => {
            application_point(left, application).or_else(|| application_point(right, application))
        }
        SyntaxProposition::Not(body)
        | SyntaxProposition::At {
            proposition: body, ..
        } => application_point(body, application),
        _ => None,
    }
}

/// The largest nonnegative constant among `application`'s arguments, such as
/// the measure `13` of `output_from(s, 0u64, 13)`: about the number of
/// further unfolds a recursion over that measure takes.
pub(super) fn largest_constant_argument(application: &ClickFunctionApplication) -> usize {
    application
        .arguments
        .iter()
        .filter_map(constant_integer)
        .filter_map(|(value, _)| usize::try_from(value).ok())
        .max()
        .unwrap_or(0)
}

/// The constant `value` of type `ty` as an expression: a machine constant, or
/// an `Integer` literal when `ty` is `None`.
fn constant_expression(value: i128, ty: Option<ConstantType>) -> Option<SyntaxTerm> {
    let value = match ty {
        None => return Some(SyntaxTerm::IntegerLiteral(value.to_string())),
        Some(ConstantType::Int8) => {
            crate::kernel::int8(OldMachineTerm::constant(i8::try_from(value).ok()? as u32))
        }
        Some(ConstantType::UInt8) => crate::kernel::uint8(OldMachineTerm::constant(u32::from(
            u8::try_from(value).ok()?,
        ))),
        Some(ConstantType::Int32) => {
            ProgramValue::Int32(OldMachineTerm::constant(i32::try_from(value).ok()? as u32))
        }
        Some(ConstantType::UInt32) => {
            ProgramValue::UInt32(OldMachineTerm::uint32_constant(u32::try_from(value).ok()?))
        }
        Some(ConstantType::Int64) => {
            ProgramValue::Int64(OldMachineTerm::int64_constant(i64::try_from(value).ok()?))
        }
        Some(ConstantType::UInt64) => {
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(u64::try_from(value).ok()?))
        }
    };
    Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
        value,
    )))
}

/// `application` with each constant argument written as its value, so
/// `output_from(s, 0u64 + 1u64, 2 - 1)` is `output_from(s, 1u64, 1)`.
fn with_constant_arguments(application: &ClickFunctionApplication) -> ClickFunctionApplication {
    ClickFunctionApplication {
        name: application.name.clone(),
        arguments: application
            .arguments
            .iter()
            .map(|argument| {
                constant_integer(argument)
                    .and_then(|(value, ty)| constant_expression(value, ty))
                    .unwrap_or_else(|| argument.clone())
            })
            .collect(),
    }
}

/// One level of a recursive function's evaluation at `application`: the arm
/// of its definition that constant `if` guards select, and the one recursive
/// call in that arm with its constant arguments evaluated, `None` at the
/// base. `None` when a guard is not constant, the function is generic or
/// not recursive, or the arm makes more than one recursive call.
pub(super) fn ground_recursion_level(
    functions: &ClickFunctionEnvironment,
    application: &ClickFunctionApplication,
) -> Option<(SyntaxTerm, Option<ClickFunctionApplication>)> {
    let definition = functions.get(&application.name)?;
    if definition.decreases().is_none()
        || !definition.type_parameters().is_empty()
        || definition.parameters().len() != application.arguments.len()
    {
        return None;
    }
    let substitutions = definition
        .parameters()
        .iter()
        .zip(&application.arguments)
        .map(|(parameter, argument)| {
            (
                parameter.binding_name(),
                crate::surface::lowering::pure_function_parameter_argument_of_type(
                    parameter, argument, None,
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut arm = crate::surface::lowering::substitute_contract_expression(
        definition.body()?,
        &substitutions,
    )
    .ok()?;
    while let SyntaxTerm::If {
        condition,
        then_branch,
        else_branch,
    } = arm
    {
        arm = if constant_guard_value(&condition)? {
            *then_branch
        } else {
            *else_branch
        };
    }
    let calls = click_function_applications(&SyntaxProposition::Value(arm.clone()), &[])
        .into_iter()
        .filter(|call| call.name == application.name)
        .collect::<Vec<_>>();
    let arm = with_constant_fields(&arm);
    match calls.as_slice() {
        [] => Some((arm, None)),
        [next] => Some((arm, Some(with_constant_arguments(next)))),
        _ => None,
    }
}

/// `expression` with each constant field of its constructors written as its
/// value, such as a string literal's byte, so the equality closure compares
/// it with a written list.
fn with_constant_fields(expression: &SyntaxTerm) -> SyntaxTerm {
    match expression {
        SyntaxTerm::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => SyntaxTerm::AlgebraicConstructor {
            algebraic_type: algebraic_type.clone(),
            variant: variant.clone(),
            arguments: arguments.iter().map(with_constant_fields).collect(),
        },
        other => constant_integer(other)
            .and_then(|(value, ty)| constant_expression(value, ty))
            .unwrap_or_else(|| other.clone()),
    }
}

/// The value of a ground recursion from its levels, each `(call, arm)` from
/// [`ground_recursion_level`], first call first: the base arm, with each
/// earlier arm's recursive call replaced by the value below it. `None` when
/// an arm holds its call where no value can be put.
pub(super) fn ground_recursion_value(
    name: &str,
    levels: &[(ClickFunctionApplication, SyntaxTerm)],
) -> Option<SyntaxTerm> {
    let ((_, base), rest) = levels.split_last()?;
    let mut value = base.clone();
    for (_, arm) in rest.iter().rev() {
        value = with_call_replaced(arm, name, &value)?;
    }
    Some(value)
}

/// `expression` with its one call of `name` replaced by `value`, through
/// constructors and `+` and `-`, the places a recursive arm holds its call.
fn with_call_replaced(
    expression: &SyntaxTerm,
    name: &str,
    value: &SyntaxTerm,
) -> Option<SyntaxTerm> {
    let replace = |expression: &SyntaxTerm| with_call_replaced(expression, name, value);
    Some(match expression {
        SyntaxTerm::Call { name: called, .. } if called == name => value.clone(),
        SyntaxTerm::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => SyntaxTerm::AlgebraicConstructor {
            algebraic_type: algebraic_type.clone(),
            variant: variant.clone(),
            arguments: arguments.iter().map(replace).collect::<Option<_>>()?,
        },
        SyntaxTerm::Add(left, right) => {
            SyntaxTerm::Add(Box::new(replace(left)?), Box::new(replace(right)?))
        }
        SyntaxTerm::Subtract(left, right) => {
            SyntaxTerm::Subtract(Box::new(replace(left)?), Box::new(replace(right)?))
        }
        other => {
            let calls = click_function_applications(&SyntaxProposition::Value(other.clone()), &[]);
            if calls.iter().any(|call| call.name == name) {
                return None;
            }
            other.clone()
        }
    })
}
