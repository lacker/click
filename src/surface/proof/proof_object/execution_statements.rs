//! Checked execution statement steps and loop-invariant bundles.

use super::*;

thread_local! {
    /// The source spelling of the bundle member the invariant-bundle planner
    /// last found open, so a refused closure names the invariant it did not
    /// prove. Diagnostic only: cleared before each closure attempt and read
    /// only on its refusal.
    static UNCLOSED_BUNDLE_MEMBER: std::cell::RefCell<Option<String>> =
        const { std::cell::RefCell::new(None) };
}

fn record_unclosed_bundle_member(spelling: Option<String>) {
    if let Some(spelling) = spelling {
        UNCLOSED_BUNDLE_MEMBER.with(|member| *member.borrow_mut() = Some(spelling));
    }
}

pub(super) fn take_unclosed_bundle_member() -> Option<String> {
    UNCLOSED_BUNDLE_MEMBER.with(|member| member.borrow_mut().take())
}

pub(super) fn describe_invariant_closure_error(error: ClickError) -> ClickError {
    let member = take_unclosed_bundle_member().or_else(|| {
        // The direct structural strategy can stop before the member planner
        // runs. Its error retains the focused goal, not an enclosing bundle.
        let goal = error.diagnostic()?.kernel_goal()?;
        (!matches!(goal, Proposition::And(_, _))).then(|| {
            crate::surface::proof_diagnostics::render::render_proposition_labeled(
                goal,
                &mut crate::surface::proof_diagnostics::render::MemoryStateLabels::ambient(),
            )
        })
    });
    let obligation = member
        .map(|member| format!("loop closure stopped with unresolved obligation: `{member}`"))
        .unwrap_or_else(|| "loop closure stopped without retaining an individual obligation; the failure applies to the bundle search".to_owned());
    // Concise reports read the diagnostic's reason, while legacy reports
    // read the summary. Restate both places, retaining the original goal,
    // checked state, budget attribution, and trace.
    error.with_rewritten_place(|reason| Some(format!("{obligation}: {reason}")))
}

/// Names the ranking members a ranked loop's bundle carries, so an explicit
/// `preserve by` body written before the `decreases` clause existed reports
/// what it now has to close instead of only that the bundle stayed open.
fn ranking_member_diagnostic(bundle: &InvariantBodyContext) -> String {
    if bundle.ranking_measures.is_empty() {
        return String::new();
    }
    // A pure component's source also serves as its declaration identity and
    // can contain structural keys. Diagnostics have the retained declaration.
    let measures = if bundle.ranking_surfaces.len() == bundle.ranking_measures.len() {
        bundle
            .ranking_surfaces
            .iter()
            .map(crate::surface::diagnostics::describe_contract_expression)
            .collect::<Vec<_>>()
    } else {
        bundle
            .ranking_measures
            .iter()
            .map(crate::kernel::ranking_measure_source)
            .collect()
    };
    let tuple = match measures.as_slice() {
        [measure] => measure.clone(),
        _ => format!("({})", measures.join(", ")),
    };
    let members = measures
        .iter()
        .map(|measure| format!("`0 <= {measure}` at the back edge"))
        .chain(std::iter::once(format!(
            "`{tuple}` decreases at the back edge"
        )))
        .collect::<Vec<_>>();
    format!(
        "; this loop declares `decreases`, so the bundle also has {}",
        members.join(", ")
    )
}

#[cfg(test)]
mod ranking_diagnostic_tests {
    use super::*;

    #[test]
    fn ranking_note_uses_written_literals_instead_of_declaration_keys() {
        let measure = ContractExpression::Add(
            Box::new(ContractExpression::Subtract(
                Box::new(ContractExpression::Binding("n".into())),
                Box::new(ContractExpression::Binding("t".into())),
            )),
            Box::new(ContractExpression::ProgramExpression(
                crate::kernel::program_expression::uint32_literal(1),
            )),
        );
        let key = crate::surface::verification::termination_measure_source(&measure);
        let component = crate::kernel::RankingComponent::PureInteger {
            source: key,
            expression: crate::kernel::SpecIntegerExpression::FromMachine(Box::new(
                crate::kernel::SpecExpression::ProgramExpression(
                    crate::kernel::program_expression::uint32_literal(1),
                ),
            )),
        };
        let mut bundle = InvariantBodyContext {
            ranking_measures: vec![component.clone()],
            ranking_surfaces: vec![measure.clone()],
            ..Default::default()
        };
        let note = ranking_member_diagnostic(&bundle);
        assert!(note.contains("1u32"), "{note}");
        assert!(!note.contains("…"), "{note}");
        assert!(!note.contains("Value("), "{note}");
        assert!(note.contains("decreases at the back edge"), "{note}");

        bundle.ranking_measures.push(component);
        bundle.ranking_surfaces.push(measure);
        let note = ranking_member_diagnostic(&bundle);
        assert!(!note.contains("Value("), "{note}");
        assert_eq!(note.matches("`0 <= ").count(), 2, "{note}");
    }
}

/// The C `if` condition standing at this frontier, spelled at that
/// statement's entry state, when the case split about to happen is exactly
/// that C branch.
///
/// A proof-level case over anything else records nothing: only a decision the
/// C program itself makes is as written as the loop guard, and only a
/// condition that matches the statement at the frontier is one of those. The
/// check is one indexed source lookup and one comparison against the written
/// condition, so it reads no fact context.
fn program_branch_condition_at_frontier(
    execution: &ExecutionProofState,
    context: &ExecutionProofContext<'_>,
    condition: &ClickProposition,
) -> Result<Option<ClickProposition>, ClickError> {
    let statement_index = execution.core.frontier.next_statement_index;
    if !context
        .constants
        .source_layout
        .statement(statement_index)
        .is_some_and(|region| matches!(region.kind, SourceStatementKind::If { .. }))
    {
        return Ok(None);
    }
    let FrontierPosition::StatementEntry { remaining } = &execution.core.frontier.position else {
        return Ok(None);
    };
    let Ok((
        ProgramStatement::If {
            condition: source, ..
        },
        _,
    )) = split_next_source_operation(remaining)
    else {
        return Ok(None);
    };
    let canonical = surface_program_condition(
        &source,
        &execution.core.state,
        Some(&execution.presentation.recorded_states),
    )?;
    if !super::same_branch_condition(&canonical, condition)
        && !(context.constants.source_layout.has_call_captures()
            && super::same_branch_condition(
                &surface_program_condition(&source, &execution.core.state, None)?,
                condition,
            ))
    {
        return Ok(None);
    }
    Ok(Some(surface_at_program_point(
        &canonical,
        &ProgramPointRef {
            region: CodeRegionRef::Region(statement_index),
            kind: ProgramPointKind::Entry,
        },
    )?))
}

impl<'a> Proof<'a> {
    /// Prepare the selected operation with all its required obligations,
    /// including prerequisites already present in the input fact index.
    /// The candidate is conditional until the driver proves those obligations
    /// at this original frontier and calls `finish_prepared_step`.
    pub(in crate::surface::proof) fn prepare_step(
        &self,
        step: &ProofStep,
    ) -> (
        Result<Self, ClickError>,
        crate::surface::proof::execution_planning::OpenObligationProbe,
    ) {
        crate::surface::proof::execution_planning::probe_step_obligations(|| {
            self.apply_primitive_step(step)
        })
    }

    /// Reports an exhausted callback script at its actual frontier. Error
    /// reporting must not execute later operations or solve their obligations.
    pub(in crate::surface::proof) fn unfinished_callback_script_error(&self) -> Option<ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        if context
            .parsed_function
            .callback_statement_sources()
            .is_empty()
        {
            return None;
        }
        Some(self.step_error(
            "the proof stops before function exit; finish the remaining C operations with `step()` or `step_until(function.exit)`, or end the script so its implicit tail runs them",
        ))
    }

    /// Restores presentation metadata for one generated bundle leaf from the
    /// two program points the loop rule itself owns. The candidate must lower
    /// alpha-equivalently to the focused kernel goal; attaching it changes no
    /// facts, proof topology, or checked proposition.
    /// The focused bundle member as a refusal names it: its source spelling,
    /// else the lowered member spelled over the back-edge locals.
    pub(super) fn bundle_member_spelling(&self) -> Option<String> {
        let presented = self.with_synthesized_bundle_member_surface();
        if let Some(surface) = presented.surface_goal() {
            let spelled = crate::surface::printing::source_click_proposition(surface);
            if !spelled.contains("__click_") {
                return Some(spelled);
            }
        }
        let goal = self.goal()?;
        let (parameters, arguments) = self.diagnostic_naming_tables();
        let mut labels = crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(
            ParameterBinding::new(&parameters, &arguments),
        );
        // A value the back-edge locals no longer hold, such as the
        // iteration's entry value of a counter, reads at the state that
        // recorded it.
        if let Some(execution) = self.execution() {
            super::register_recorded_state_names(
                &mut labels,
                &execution.presentation.recorded_states,
            );
        }
        // The pass's own count, `iterations`.
        if let Some(crate::kernel::IntegerTerm::Variable(variable)) = self
            .execution_context()
            .and_then(|context| context.constants.invariant_body_context.as_deref())
            .and_then(|bundle| bundle.iterations.as_ref())
        {
            labels.integer_source_name(*variable, crate::surface::LOOP_ITERATIONS_NAME.to_string());
        }
        let mut lowered = crate::surface::proof_diagnostics::render::render_proposition_labeled(
            goal,
            &mut labels,
        );
        lowered.push_str(&labels.trace_legend());
        // The back-edge locals do not name a value read at an earlier
        // state, which the lowered spelling elides. The synthesized form
        // names that state even where it does not lower back exactly, as
        // an unsigned order does not.
        if lowered.contains('…')
            && let Some(surface) = self.bundle_member_surface(goal, false)
        {
            let spelled = crate::surface::printing::refusal_click_proposition(&surface);
            if !spelled.contains("__click_") && !spelled.contains('…') {
                return Some(spelled);
            }
        }
        Some(lowered)
    }

    fn with_synthesized_bundle_member_surface(&self) -> Self {
        if self.surface_goal().is_some() {
            return self.clone();
        }
        let Some(goal) = self.goal() else {
            return self.clone();
        };
        let surface = self.synthesized_bundle_member_surface(goal);
        let Some(surface) = surface else {
            return self.clone();
        };
        let Some(state) = self
            .state
            .with_focused_proposition_presentation(|presentation| PropositionPresentation {
                surface: Some(Arc::new(surface)),
                ..presentation.clone()
            })
        else {
            return self.clone();
        };
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        }
    }

    /// The back-edge bundle's members as the loop head writes them, split
    /// at conjunctions as the bundle's leaves are: each declared invariant
    /// whole and by conjunct, without the guards of the invariants declared
    /// before it, which a member's guards are matched to one by one, so the
    /// forms stay linear in the declarations; one `0 <= m` per
    /// `decreases` component, then the descent member
    /// ([`ranking_descent_surface`]), when `ranking` asks for them. None
    /// outside a loop preservation proof.
    pub(in crate::surface::proof) fn written_bundle_member_surfaces(
        &self,
        ranking: bool,
    ) -> Option<Vec<ClickProposition>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let bundle = context.constants.invariant_body_context.as_deref()?;
        let mut members = Vec::new();
        // The back edge owes each invariant one pass on: where the head
        // writes `iterations`, the member reads `iterations + 1`. That form
        // is offered first, and like every written form is kept only when
        // it lowers back to its leaf.
        let next_pass = BTreeMap::from([(
            crate::surface::LOOP_ITERATIONS_NAME.to_string(),
            ContractExpression::Add(
                Box::new(ContractExpression::Binding(
                    crate::surface::LOOP_ITERATIONS_NAME.to_string(),
                )),
                Box::new(ContractExpression::IntegerLiteral("1".to_string())),
            ),
        )]);
        let one_pass_on = bundle
            .declared_invariant_surfaces
            .iter()
            .map(|invariant| {
                crate::surface::lowering::substitute_click_proposition(invariant, &next_pass)
            })
            .collect::<Result<Vec<_>, _>>()
            .ok()
            .filter(|shifted| shifted != &bundle.declared_invariant_surfaces);
        for declared in one_pass_on
            .iter()
            .chain(std::iter::once(&bundle.declared_invariant_surfaces))
        {
            for invariant in declared {
                // The whole invariant, as a later member's guard reads it,
                // and then its conjuncts, which are the bundle's leaves.
                let mut pending = vec![invariant.clone()];
                let mut whole = true;
                while let Some(member) = pending.pop() {
                    match member {
                        ClickProposition::And(left, right) => {
                            if std::mem::take(&mut whole) {
                                members.push(ClickProposition::And(left.clone(), right.clone()));
                            }
                            pending.push(*right);
                            pending.push(*left);
                        }
                        member => {
                            whole = false;
                            members.push(member);
                        }
                    }
                }
            }
        }
        if ranking && bundle.ranking_surfaces.len() == bundle.ranking_measures.len() {
            for component in &bundle.ranking_surfaces {
                members.push(ClickProposition::Comparison {
                    left: ContractExpression::IntegerLiteral("0".to_string()),
                    operator: ComparisonOperator::LessEqual,
                    right: component.clone(),
                });
            }
            members.extend(ranking_descent_surface(bundle));
        }
        Some(members)
    }

    /// One bundle member's source form, synthesized at the current state
    /// with the iteration entry, and failing that the loop entry, as the one
    /// further state, and kept only when it lowers alpha-equivalently to
    /// `goal`. A member at the loop entry has no source form in the whole
    /// bundle's synthesis, which names only the iteration entry, so a
    /// written `both` over a bundle reaches its members through this too.
    pub(in crate::surface::proof) fn synthesized_bundle_member_surface(
        &self,
        goal: &Proposition,
    ) -> Option<ClickProposition> {
        self.bundle_member_surface(goal, true)
    }

    /// [`Self::synthesized_bundle_member_surface`], or with `checked` false
    /// the synthesized form whether or not it lowers back to `goal`. Only a
    /// refusal reads the unchecked form, to name the states a member
    /// compares; nothing proves or records it.
    fn bundle_member_surface(&self, goal: &Proposition, checked: bool) -> Option<ClickProposition> {
        let context = self.execution_context()?;
        let execution = self.execution()?;
        let bundle = context.constants.invariant_body_context.as_deref()?;
        let synthesize_at = |state: &ExecutionState, selector: &ProgramPointSelector| {
            let synthesize = || {
                crate::surface::proof::surface_synthesis::synthesize_surface_proposition_at_entry_post_and_state(
                    goal,
                    context.parameter_binding(),
                    context.old_reference_state(&execution.core.frontier, &execution.core.state),
                    &execution.core.state,
                    Some((state, selector)),
                )
            };
            let accepted = |surface: &ClickProposition| {
                !checked
                    || self
                        .lower_surface_goal(surface, "loop invariant bundle member")
                        .ok()
                        .is_some_and(|lowered| {
                            crate::kernel::proof::propositions_are_alpha_equal(&lowered, goal)
                        })
            };
            if bundle.binder_names.is_empty() {
                return synthesize().filter(accepted);
            }
            // A binder takes the name its invariant wrote. The generated name
            // remains the fallback, tried only when the written spelling came
            // out different and does not lower back to this member.
            let written = crate::surface::proof::surface_synthesis::with_synthesis_binder_names(
                &bundle.binder_names,
                synthesize,
            )?;
            if accepted(&written) {
                return Some(written);
            }
            synthesize().filter(|generated| generated != &written && accepted(generated))
        };
        bundle
            .iteration_entry_selector
            .as_ref()
            .and_then(|selector| synthesize_at(&bundle.iteration_entry_state, selector))
            .or_else(|| {
                bundle
                    .loop_entry_selector
                    .as_ref()
                    .and_then(|selector| synthesize_at(&bundle.loop_entry_state, selector))
            })
            .or_else(|| {
                let written = ranking_descent_surface(bundle)?;
                (!checked
                    || self
                        .lower_surface_goal(&written, "loop invariant bundle member")
                        .ok()
                        .is_some_and(|lowered| {
                            crate::kernel::proof::propositions_are_alpha_equal(&lowered, goal)
                        }))
                .then_some(written)
            })
    }

    /// The value produced by the current frontier statement. A bare step
    /// accepts a scalar assignment or a retained step result. A step with
    /// a callee or contract selection accepts only a call result.
    ///
    /// A call whose result the rest of its statement reads is a call step of
    /// its own, and its result is that step's. A call in statement position
    /// discards its result; naming it is an error rather than a silent no-op.
    fn frontier_result(
        &self,
        name: &String,
        allow_non_call: bool,
    ) -> Result<FrontierResult, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // The result hides an earlier proof-local value of its name, as any
        // proof binder does; a C variable of that name stays the program's.
        if execution.core.state.locals().contains_name(name)
            || context.constants.source_layout.has_parameter_name(name)
        {
            return Err(self.step_error(format!(
                "`{name}` names a C variable here; a proof binder cannot hide it, since execution keeps reading the program's `{name}`; choose another name"
            )));
        }
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "step",
        )?;
        match statement {
            ProgramStatement::Assign { name, .. } if allow_non_call => Ok(FrontierResult::Local(name)),
            ProgramStatement::CallConstruct { target, .. } => {
                Ok(FrontierResult::Local(target))
            }
            ProgramStatement::CallResult { call, .. } => Ok(FrontierResult::Retained(call)),
            ProgramStatement::StepValue { aggregate_layout: None, steps, .. }
                if allow_non_call && !steps.is_empty() =>
            {
                // All of the step's destination slots hold the same evaluated value.
                Ok(FrontierResult::Retained(steps[0]))
            }
            _ if allow_non_call => Err(self.step_error(format!(
                "`let {{ result: {name} }} = step()` requires a scalar assignment, a used call result, or a retained scalar value at the frontier"
            ))),
            _ => Err(self.step_error(format!(
                "`let {{ result: {name} }} = step(...)` names a call result, but this call's result is unused"
            ))),
        }
    }

    /// `expression` evaluated at the frontier's state, as a call step's map
    /// value or the argument of the call it runs is: once, through the
    /// kernel.
    fn evaluate_at_frontier(
        &self,
        context: &ExecutionProofContext<'_>,
        expression: &ContractExpression,
        what: &str,
    ) -> Result<ProgramValue, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error(format!("{what} needs an execution state")))?;
        let state = &*execution.core.state;
        let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
        let pre_state = context.old_reference_state(&execution.core.frontier, state);
        let values = parameter_values(context.parameter_binding())?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            &state.program_point(),
        );
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
        evaluate_fixed_state_expression_through_kernel(
            &expression,
            self.facts().assumptions(),
            ContractEnvironment::new(&values, &array_refs)
                .with_parameters(context.parameter_binding()),
            FixedStateFrame::new(
                pre_state,
                state,
                None,
                &execution.presentation.recorded_states,
            ),
            context.spec_definitions,
            &BTreeSet::new(),
        )
        .map_err(|message| self.step_error(format!("{what}: {message}")))
    }

    pub(in crate::surface::proof) fn apply_execution_statement_step_with_policy(
        &self,
        step: ProofStep,
        prerequisite_policy: StatementPrerequisitePolicy,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step` requires an execution-frontier proof"));
        };
        let addressed_context = self
            .site
            .tactic_index()
            // Loop phase drivers already attribute their own local script.
            // The enclosing proof site still names the outer loop tactic.
            .filter(|_| context.constants.invariant_body_context.is_none())
            .map(|index| context.with_tactic_index(index));
        let context = addressed_context.as_ref().unwrap_or(context);
        // `step(callee, { ... })` runs the call at the frontier, which must
        // call `callee`; its arguments are that call's.
        let frontier_call = match &step {
            ProofStep::StepCall(transport) if transport.is_frontier() => {
                Some(self.frontier_call_for_named_function(context, transport)?)
            }
            _ => None,
        };
        // Resolve this statement's result slot before checking the step.
        // Only its checked successor value is bound below. The assignment
        // or call is exactly the current frontier; nothing is searched.
        let result_target = match &step {
            ProofStep::StepBind(name) => Some((name.clone(), self.frontier_result(name, true)?)),
            ProofStep::StepCall(transport) => match transport.result() {
                Some(name) => {
                    let name = name.to_string();
                    let target = self.frontier_result(&name, false)?;
                    Some((name, target))
                }
                None => None,
            },
            _ => None,
        };
        let selected_environment;
        let selected_context;
        let context = if let ProofStep::StepContract(application) = &step {
            let name = &application.name;
            if context
                .function_environment
                .get_function_contract(name)
                .is_none()
            {
                return Err(self.step_error(format!("unknown call contract `{name}`")));
            }
            let definition = context
                .spec_definitions
                .predicates
                .contract_definition(name)
                .ok_or_else(|| self.step_error(format!("unknown call contract `{name}`")))?;
            let parameters = definition.proof_parameters.as_deref().unwrap_or(&[]);
            let handle_names = || {
                parameters
                    .iter()
                    .map(|parameter| match parameter {
                        ResourceClause::Named { binding, .. } => format!("`{}`", binding.name),
                        _ => unreachable!(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            // Entries name the contract's handles; each handle takes exactly
            // one entry, matched by name in one lookup per entry.
            let mut by_handle = BTreeMap::new();
            for argument in &application.arguments {
                crate::instrumentation::record_deterministic_work(1);
                if !parameters.iter().any(|parameter| {
                    matches!(parameter, ResourceClause::Named { binding, .. }
                        if binding.name == argument.handle)
                }) {
                    return Err(self.step_error(if parameters.is_empty() {
                        format!(
                            "contract `{name}` declares no resource handles; write `step({name})`"
                        )
                    } else {
                        format!(
                            "contract `{name}` has no resource handle `{}`; its handles are {}",
                            argument.handle,
                            handle_names()
                        )
                    }));
                }
                if by_handle
                    .insert(argument.handle.as_str(), argument)
                    .is_some()
                {
                    return Err(self.step_error(format!(
                        "contract `{name}` handle `{}` is bound twice",
                        argument.handle
                    )));
                }
            }
            let mut arguments = Vec::with_capacity(parameters.len());
            for parameter in parameters {
                let ResourceClause::Named { binding, .. } = parameter else {
                    unreachable!()
                };
                let Some(argument) = by_handle.get(binding.name.as_str()) else {
                    // A `produces` handle is introduced by the `let` pattern,
                    // not supplied in the map.
                    let produced = definition
                        .function_block()
                        .ensures()
                        .iter()
                        .filter(|ensure| !ensure.borrowed())
                        .filter_map(|ensure| match ensure.ensure() {
                            Ensure::Resource(ResourceClause::Named { binding, .. }) => {
                                Some(binding.name.clone())
                            }
                            _ => None,
                        })
                        .collect::<BTreeSet<_>>();
                    let entries = |produced_side: bool| {
                        parameters
                            .iter()
                            .filter_map(|parameter| match parameter {
                                ResourceClause::Named { binding, .. }
                                    if produced.contains(&binding.name) == produced_side =>
                                {
                                    Some(format!("{}: ...", binding.name))
                                }
                                _ => None,
                            })
                            .collect::<Vec<_>>()
                            .join(", ")
                    };
                    let spelling = if produced.is_empty() {
                        format!("step({name}, {{ {} }})", entries(false))
                    } else {
                        format!(
                            "let {{ {} }} = step({name}, {{ {} }})",
                            entries(true),
                            entries(false)
                        )
                    };
                    return Err(self.step_error(format!(
                        "contract `{name}` declares resource handles; write `{spelling}` with one instance for each of {}",
                        handle_names()
                    )));
                };
                arguments.push(*argument);
            }
            let mut identities = BTreeSet::new();
            for (parameter, argument) in parameters.iter().zip(&arguments) {
                let ResourceClause::Named { binding, resource } = parameter else {
                    unreachable!()
                };
                let ResourceClause::Declared { name: expected, .. } = resource.as_ref() else {
                    unreachable!()
                };
                if argument.resource_name != *expected {
                    return Err(self.step_error(format!(
                        "contract `{name}` handle `{}` expects resource `{expected}`, got `{}`",
                        binding.name, argument.resource_name
                    )));
                }
                if !identities.insert(argument.identity) {
                    return Err(self.step_error(
                        "an exclusive instance cannot supply two contract resource handles",
                    ));
                }
            }
            selected_environment = context
                .function_environment
                .clone()
                .with_selected_call_contract(name)
                .with_selected_call_resource_arguments(
                    arguments.iter().map(|argument| argument.identity).collect(),
                );
            selected_context = context.with_loop_binding(
                context.function_block,
                context.function,
                &selected_environment,
            );
            &selected_context
        } else if let ProofStep::StepCall(transport) = &step {
            let callee = transport.callee();
            // One lookup per written entry builds the whole binding; the
            // kernel consults nothing else at this call.
            let mut bindings = BTreeMap::new();
            for binding in transport.binders().iter().chain(transport.produced()) {
                crate::instrumentation::record_deterministic_work(1);
                crate::kernel::model_fields::register_instance_spelling(
                    binding.identity(),
                    binding.instance(),
                );
                if bindings
                    .insert(binding.binder_identity(), binding.identity())
                    .is_some()
                {
                    return Err(self.step_error(format!(
                        "duplicate binder `{}` in the call map",
                        binding.binder()
                    )));
                }
            }
            // A runtime type binder names the resource type as the call's
            // state reads it.
            let mut type_arguments = BTreeMap::new();
            for (_, identity, resource) in transport.type_arguments() {
                let ResourceClause::Declared { name, .. } = resource else {
                    return Err(self.step_error("a type binder names a declared resource type"));
                };
                let state = &*self
                    .execution()
                    .ok_or_else(|| self.step_error("a type binder needs an execution state"))?
                    .core
                    .state;
                let fact = crate::surface::lowering::lower_resource_clause_at_state(
                    resource,
                    context.parameter_binding(),
                    state,
                )?;
                let crate::kernel::Resource::Composite { arguments, .. } = fact.resource() else {
                    return Err(self.step_error(format!(
                        "type binder `{name}` must name a resource with a body"
                    )));
                };
                let schema = context
                    .resource_environment
                    .get(name)
                    .and_then(|definition| definition.field_schema().cloned())
                    .or_else(|| crate::kernel::ResourceFieldSchema::new(Vec::new()))
                    .ok_or_else(|| self.step_error("resource type has no field schema"))?;
                type_arguments.insert(
                    *identity,
                    crate::kernel::ResourceDescription::new(
                        name.clone(),
                        arguments.clone(),
                        schema,
                    ),
                );
            }
            // Each entry gives a callee's `let` value parameter its value,
            // evaluated at the call's state; the kernel still requires the
            // parameter's clauses at it.
            let mut selected_values = Vec::new();
            for (parameter, expression) in transport.value_arguments() {
                crate::instrumentation::record_deterministic_work(1);
                let value = self.evaluate_at_frontier(
                    context,
                    expression,
                    &format!("call map value `{parameter}`"),
                )?;
                selected_values.push((parameter.clone(), value));
            }
            let mut environment = context.function_environment.clone();
            if !selected_values.is_empty() {
                let function = frontier_call
                    .as_ref()
                    .map_or(callee, |call| call.callee.as_str());
                environment = environment.with_selected_call_values(function, selected_values);
            }
            let arity = if let Some(call) = &frontier_call {
                call.arguments.len()
            } else if transport.is_named_contract() {
                let definition = context
                    .spec_definitions
                    .predicates
                    .contract_definition(callee)
                    .ok_or_else(|| self.step_error(format!("unknown call contract `{callee}`")))?;
                environment = environment.with_selected_call_contract(callee);
                definition.function_block().signature().parameters().len()
            } else {
                transport.arguments().len()
            };
            let execution_callee = if let Some(call) = &frontier_call {
                call.callee.as_str()
            } else if transport.is_named_contract() {
                callee
            } else {
                context
                    .spec_definitions
                    .predicates
                    .function_execution_name(callee)
            };
            selected_environment = environment.with_selected_call_binders_and_types(
                execution_callee,
                arity,
                bindings,
                type_arguments,
            );
            selected_context = context.with_loop_binding(
                context.function_block,
                context.function,
                &selected_environment,
            );
            &selected_context
        } else {
            context
        };
        self.require_execution_frontier("`step`")?;
        // A produced instance of `step(callee, { ... })` reads its resource
        // arguments as `name.parameter`: each is the frontier call's argument,
        // evaluated before the call runs, bound below as the result is.
        let mut produced_arguments = Vec::new();
        if let (ProofStep::StepCall(transport), Some(call)) = (&step, &frontier_call) {
            for produced in transport.produced() {
                for (name, argument) in produced.call_arguments().iter().zip(&call.arguments) {
                    crate::instrumentation::record_deterministic_work(1);
                    let value = self.evaluate_at_frontier(
                        context,
                        &ContractExpression::ProgramExpression(argument.clone()),
                        &format!("call argument `{name}`"),
                    )?;
                    produced_arguments.push((
                        name.clone(),
                        ContractExpression::ProgramExpression(ProgramExpression::Value(value)),
                    ));
                }
            }
        }
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // Every statement step executes in the whole proof context.
        let fact_context = Some(self.facts().assumptions());
        let mut checked = check_statement_step_with_policy(
            &mut execution,
            context,
            self.facts(),
            fact_context,
            prerequisite_policy,
        )?;
        // A fact the statement introduces (a callee's `ensures`, a store's
        // value) is recorded under its readable spelling at the successor
        // state, so a later premise can name it without re-lowering it against
        // another memory. Output-sized work: one synthesis per introduced
        // fact.
        for fact in &checked.added_facts {
            if let Some(surface) = synthesize_surface_proposition(
                fact,
                context.parameter_binding(),
                &checked.execution.core.state,
            ) {
                // At a call successor, a synthesized `old(...)` names the
                // callee's entry state, while the same surface syntax in
                // the caller names the caller's function entry. Do not cache
                // that ambiguous spelling as caller-state origin. Explicit
                // MemoryState-qualified forms (including proof marks) retain the exact
                // call-frontier identity needed to name such a fact later.
                if proposition_contains_old_expression(&surface) {
                    continue;
                }
                let _ = checked
                    .execution
                    .presentation
                    .surface_propositions
                    .record_lowering(&surface, fact);
            }
        }
        // Bind the result with one indexed read from the checked successor,
        // using either the assigned local or the step's result slot.
        let result_binding = match &result_target {
            Some((name, target)) => {
                let state = &checked.execution.core.state;
                let value = match target {
                    FrontierResult::Local(target) => state
                        .locals()
                        .get(target)
                        .map(|value| value.clone().into_native()),
                    FrontierResult::Retained(step) => state
                        .step_result(*step)
                        .map(|value| value.clone().into_native()),
                }
                .ok_or_else(|| {
                    self.step_error(format!(
                        "`let {{ result: {name} }} = step(...)` found no retained result"
                    ))
                })?;
                Some((
                    name.clone(),
                    ContractExpression::ProgramExpression(ProgramExpression::Value(value)),
                ))
            }
            None => None,
        };
        let added_facts = checked.added_facts;
        let state = self
            .state
            .publish_checked_frontier_transition(
                checked.facts,
                checked.execution,
                added_facts.clone(),
                added_facts,
            )
            .map_err(|error| self.execution_update_error("`step`", error))?;
        let state = if result_binding.is_none() && produced_arguments.is_empty() {
            state
        } else {
            let mut locals = state.locals().clone();
            for (name, value) in result_binding.into_iter().chain(produced_arguments) {
                locals.set_values(locals.values.with_inserted(name, value));
            }
            state.with_locals(locals)
        };
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(&self.node, self.focused_branch_id(), Arc::new(step)),
        })
    }

    /// `name(args, { binder: instance })`: one application of a user-defined
    /// tactic at the execution frontier.
    ///
    /// The tactic's verified rule is applied by the kernel with no C
    /// statement; the binder map is the whole binding, exactly as for a call
    /// step, and every argument is lowered at the frontier as a fold field
    /// is. Every precondition must already be an available fact.
    pub(in crate::surface::proof) fn apply_execution_user_tactic(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        let ProofStep::UserTactic(application) = &step else {
            unreachable!("only a tactic application reaches this step")
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "a tactic is applied in a C function or tactic proof in this release",
            ));
        };
        self.require_execution_frontier("a tactic application")?;
        let callee = application.callee();
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let parameters = context
            .function_environment
            .get_function(callee)
            .ok_or_else(|| self.step_error(format!("unknown tactic `{callee}`")))?
            .parameters()
            .to_vec();
        if parameters.len() != application.arguments().len() {
            return Err(self.step_error(format!(
                "tactic `{callee}` expects {} argument(s), got {}",
                parameters.len(),
                application.arguments().len()
            )));
        }
        let mut bindings = BTreeMap::new();
        for binding in application.binders().iter().chain(application.produced()) {
            crate::instrumentation::record_deterministic_work(1);
            if bindings
                .insert(binding.binder_identity(), binding.identity())
                .is_some()
            {
                return Err(self.step_error(format!(
                    "duplicate binder `{}` in the tactic's map",
                    binding.binder()
                )));
            }
        }
        let environment = context
            .function_environment
            .clone()
            .with_selected_call_binders(callee, parameters.len(), bindings);
        let before = &*execution.core.state;
        let pre_state = context.old_reference_state(&execution.core.frontier, before);
        let values = parameter_values(context.parameter_binding())?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            &before.program_point(),
        );
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, before);
        let mut arguments = Vec::with_capacity(parameters.len());
        for (parameter, argument) in parameters.iter().zip(application.arguments()) {
            let argument = self.substitute_fixed_state_locals_in_expression(argument)?;
            // As at resource and pure-function parameters, the literal `0`
            // denotes a typed null pointer here. Do not coerce arbitrary
            // integer expressions, even when their evaluated value is zero.
            if parameter.program_type().is_pointer()
                && matches!(&argument, ContractExpression::IntegerLiteral(text) if text == "0")
            {
                arguments.push(ProgramValue::typed_pointer(
                    crate::kernel::Address::null(),
                    parameter.program_type(),
                ));
                continue;
            }
            let (value, obligations) = capture_resource_field_initializer(
                &argument,
                &crate::kernel::ResourceFieldType::Program(parameter.program_type()),
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &array_refs)
                    .with_parameters(context.parameter_binding()),
                pre_state,
                before,
                &execution.presentation.recorded_states,
                context.spec_definitions,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "tactic `{callee}` argument `{}`: {message}",
                    parameter.name()
                ))
            })?;
            for obligation in obligations {
                crate::surface::proof::execution_planning::refuse_or_record_open_obligation(
                    self.step_error(format!(
                        "tactic `{callee}` argument `{}` has an unproved evaluation obligation",
                        parameter.name()
                    ))
                    .with_unresolved_requirement(&obligation),
                )?;
            }
            let crate::kernel::AlgebraicValue::Program(value) = value else {
                unreachable!("a C parameter captures a C value")
            };
            arguments.push(value);
        }
        let before_state = (*execution.core.state).clone();
        let context_parameters = context.parsed_function.parameters();
        let context_arguments = context.arguments;
        let (state, facts) = execution
            .core
            .record_tactic_application(
                context.function,
                context.arguments,
                self.facts(),
                callee,
                &arguments,
                &environment,
            )
            .map_err(|refusal| match refusal {
                crate::kernel::TacticApplicationRefusal::MissingRequirement(
                    requirement,
                    context,
                ) => {
                    let spelling = synthesize_surface_proposition(
                        &requirement,
                        ParameterBinding::new(context_parameters, context_arguments),
                        &before_state,
                    )
                    .map(|proposition| {
                        crate::surface::diagnostics::describe_click_proposition(&proposition)
                    })
                    .unwrap_or_else(|| {
                        crate::surface::proof_diagnostics::render::render_proposition(&requirement)
                    });
                    let owed = context.map_or_else(String::new, |context| format!(" ({context})"));
                    self.step_error(format!(
                        "tactic `{callee}` requires `{spelling}`{owed}, which is not an available \
                         fact here; establish it first, for example with `have`"
                    ))
                }
                crate::kernel::TacticApplicationRefusal::Refused(message) => {
                    self.step_error(message)
                }
            })?;
        execution.core.state = state.into();
        let added_facts = facts.introduced_since(self.facts()).unwrap_or_default();
        let state = self
            .state
            .publish_checked_frontier_transition(facts, execution, added_facts.clone(), added_facts)
            .map_err(|error| self.execution_update_error("a tactic application", error))?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(&self.node, self.focused_branch_id(), Arc::new(step)),
        })
    }

    /// The call at the frontier that `step(callee, { ... })` runs, once it is
    /// shown to call `callee` and each value entry to name one of the
    /// callee's `let` value parameters: one statement read, then one pass
    /// over those parameters per entry. The C name identifies the formatted-output
    /// function of whatever format the call passes.
    fn frontier_call_for_named_function(
        &self,
        context: &ExecutionProofContext<'_>,
        transport: &CallBinderTransport,
    ) -> Result<FrontierCall, ClickError> {
        let written = transport.callee();
        let remaining =
            self.execution()
                .and_then(|execution| match &execution.core.frontier.position {
                    FrontierPosition::FunctionEntry => Some(context.function.body()),
                    FrontierPosition::StatementEntry { remaining } => Some(remaining.as_ref()),
                    _ => None,
                });
        // A `try` or an unwind cleanup does not introduce an executable step.
        // Select the same first operation that ordinary `step()` will execute,
        // leaving the statement intact for the kernel's exception
        // continuation. Borrow only the leading source path: splitting or
        // cloning each one here would also copy its handler or cleanup.
        let mut operation = remaining;
        loop {
            operation = match operation {
                Some(ProgramStatement::Seq(statements)) => Some(statements.first()),
                Some(
                    ProgramStatement::TryCatchInt32 { try_body, .. }
                    | ProgramStatement::UnwindCleanup { body: try_body, .. },
                ) => Some(try_body.as_ref()),
                _ => break,
            };
            crate::instrumentation::record_deterministic_work(1);
        }
        let call = operation.and_then(|statement| match statement {
            ProgramStatement::Call {
                function_name,
                arguments,
                ..
            }
            | ProgramStatement::CallConstruct {
                function_name,
                arguments,
                ..
            }
            | ProgramStatement::CallResult {
                function_name,
                arguments,
                ..
            } => Some(FrontierCall {
                callee: function_name.clone(),
                arguments: arguments.clone(),
            }),
            _ => None,
        });
        let names_written = |callee: &str| {
            callee == written
                || crate::surface::call_source_spelling(callee) == written
                || context
                    .spec_definitions
                    .predicates
                    .function_execution_name(written)
                    == callee
                || crate::languages::c::formatted_output::function_format(callee)
                    .is_some_and(|(function, _)| function.source_name() == written)
        };
        let Some(call) = call.filter(|call| names_written(&call.callee)) else {
            return Err(self.step_error(format!(
                "`{transport}` requires a call to `{written}` at the current frontier"
            )));
        };
        if transport.value_arguments().is_empty() {
            return Ok(call);
        }
        let named = || {
            crate::languages::c::formatted_output::describe_function(&call.callee)
                .unwrap_or_else(|| format!("`{written}`"))
        };
        let Some(function) = context.function_environment.get_function(&call.callee) else {
            return Err(self.step_error(format!(
                "`{transport}` gives values to {}, which has no Click contract",
                named()
            )));
        };
        let parameters = function.contract_interface().value_parameters();
        for (name, _) in transport.value_arguments() {
            crate::instrumentation::record_deterministic_work(1);
            if !parameters.iter().any(|parameter| parameter.name() == name) {
                return Err(
                    self.step_error(format!("{} declares no value parameter `{name}`", named()))
                );
            }
        }
        Ok(call)
    }

    pub(super) fn apply_execution_mark(&self, name: &str) -> Result<KernelProofHandle, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`mark`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let mut presentation = execution.presentation.clone();
        let selector = ProgramPointSelector::Mark(name.to_string());
        if presentation.recorded_states.contains_key(&selector) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        presentation
            .recorded_states
            .insert(selector, (*execution.core.state).clone());
        self.state
            .replace_frontier_presentation(presentation)
            .map_err(|error| self.execution_update_error("`mark`", error))
    }

    /// This frontier with the by-value parameters of the call `candidate`
    /// prepared, as that preparation bound them: the call's parameter point
    /// (`R.parameter(name)`), copied from the candidate's recorded states.
    /// The call's requirements read those parameters, so a step proves them
    /// here, at its pre-state, with that point named. Only the presentation
    /// changes; the facts and the proof node are this frontier's.
    pub(in crate::surface::proof) fn with_prepared_call_parameters(
        &self,
        candidate: &Self,
    ) -> Self {
        let (Some(execution), Some(prepared)) = (self.execution(), candidate.execution()) else {
            return self.clone();
        };
        let Some(point) = &prepared.presentation.surface_record.last_call_parameters else {
            return self.clone();
        };
        let Some(bound) = prepared.presentation.recorded_states.get(point) else {
            return self.clone();
        };
        if execution.presentation.recorded_states.get(point) == Some(bound)
            && execution
                .presentation
                .surface_record
                .last_call_parameters
                .as_ref()
                == Some(point)
        {
            return self.clone();
        }
        let point = point.clone();
        let mut presentation = execution.presentation.clone();
        presentation
            .recorded_states
            .insert(point.clone(), bound.clone());
        presentation.surface_record.last_call_parameters = Some(point);
        let Ok(state) = self.state.replace_frontier_presentation(presentation) else {
            return self.clone();
        };
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        }
    }

    /// Publish a prepared operation after its caller has proved
    /// every recorded obligation at this original frontier. The candidate must
    /// never be used as the context for those proofs. A refused operation has
    /// no retained successor and cannot be completed by re-executing it.
    fn finish_prepared_step(
        &self,
        prepared: Result<Self, ClickError>,
        proved: &Self,
        discharged: &[UnresolvedRequirement],
    ) -> Result<Self, ClickError> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("finish_prepared_step");
        let mut candidate = prepared?;
        // Every successful fold retains either its exchange or its outcome
        // definition-law presentation while the driver proves its premises.
        let prepared_fold = candidate
            .execution()
            .is_some_and(|execution| execution.core.has_prepared_fold());
        let mut introduced = proved
            .facts()
            .introduced_since(self.facts())
            .expect("obligation proofs extend their original fact context");
        // A call precondition can already belong to the input context. Its
        // proof still supplies evidence to the execution path, whose retained
        // facts are separate from the frontier's persistent input context.
        // Other obligation adapters (notably assertion false-path goals)
        // retain the facts their proofs actually introduce above.
        introduced.extend(
            discharged
                .iter()
                .filter(|requirement| requirement.call_site.is_some())
                .map(|requirement| requirement.proposition.clone()),
        );
        let original = self
            .execution()
            .expect("statement preparation has a frontier");
        let proven = proved
            .execution()
            .expect("obligation proofs retain the frontier");
        let mut execution = candidate
            .execution()
            .expect("prepared statement has a successor")
            .clone();
        let facts = if execution.core.has_prepared_return_fold() {
            execution
                .core
                .finish_prepared_return_fold(&proven.core, proved.facts())
                .map_err(|error| self.step_error(error))?
        } else if prepared_fold {
            execution.core.finish_prepared_instance_fold(proved.facts())
        } else {
            introduced
                .iter()
                .fold(candidate.facts().clone(), |facts, fact| {
                    facts.with_kernel_checked_fact(fact.clone())
                })
        };
        // `have` publication keeps its source spelling and certificate facts
        // beside the logical context. Carry only the appended suffix, preserving
        // the candidate's new call bindings, states, and typed read evidence.
        let retained = proven
            .presentation
            .surface_record
            .retained_have_facts
            .introduced_since(&original.presentation.surface_record.retained_have_facts)
            .expect("obligation proofs append retained facts");
        for fact in retained {
            execution
                .presentation
                .surface_propositions
                .record_lowering(
                    proven.presentation.surface_propositions.surface(&fact)?,
                    &fact,
                )?;
            execution.presentation.surface_record.retained_have_facts = execution
                .presentation
                .surface_record
                .retained_have_facts
                .with_kernel_checked_fact(fact);
        }
        if prepared_fold {
            candidate.state = candidate
                .state
                .publish_checked_focused_transition(
                    candidate
                        .focused_obligation()
                        .expect("prepared fold retains its goal")
                        .clone(),
                    facts,
                    Some(Arc::new(execution)),
                    candidate.state().added_facts().to_vec(),
                    candidate.state().checked_facts().to_vec(),
                )
                .map_err(|_| self.step_error("prepared fold lost its selected goal"))?;
            return Ok(candidate);
        }
        // A completing statement also saved its conditional obligations in
        // the function outcome. Publish the proved input delta on those new
        // outcomes so contract certification sees the evidence too. Earlier
        // loop returns belong to their own paths, not this frontier.
        if let Some(completed) = execution.core.frontier.execution() {
            let additional = introduced
                .iter()
                .cloned()
                .map(ExecutionPureFact::new)
                .collect::<crate::kernel::ExecutionFacts>();
            let paths = completed
                .paths()
                .iter()
                .enumerate()
                .map(|(index, path)| {
                    if execution.evidence_for_outcome(index).loop_return.is_some() {
                        path.clone()
                    } else {
                        crate::kernel::program_function_execution_candidate_with_additional_facts(
                            path,
                            &additional,
                        )
                    }
                })
                .collect();
            let completed =
                crate::kernel::program_function_execution_candidates_from_retained_paths(
                    completed.state().clone(),
                    completed.function().clone(),
                    completed.arguments().to_vec(),
                    paths,
                );
            if let Some(leaf) = &mut execution.presentation.checked_leaf_facts {
                Arc::make_mut(leaf).0 = completed
                    .candidate_at(0)
                    .expect("one checked outcome")
                    .clone();
            }
            execution.core.frontier.position = FrontierPosition::FunctionExit {
                execution: completed,
            };
        }
        // A terminal statement has already captured its facts for contract
        // certification. Extend that retained context by the checked input
        // delta too; otherwise it still describes the conditional probe.
        if let Some(leaf) = &mut execution.presentation.checked_leaf_facts {
            let (_, leaf_facts, _) = Arc::make_mut(leaf);
            for fact in &introduced {
                *leaf_facts = leaf_facts.with_kernel_checked_fact(fact.clone());
            }
        }
        let state = candidate
            .state
            .publish_checked_frontier_transition(
                facts,
                execution,
                candidate.state().added_facts().to_vec(),
                candidate.state().checked_facts().to_vec(),
            )
            .map_err(|error| self.execution_update_error("prepared step", error))?;
        candidate.state = state;
        Ok(candidate)
    }

    /// Construct one primitive transition. Preparation collects its required
    /// propositions; only the driver supplies their proofs and publishes the
    /// retained successor. A refusal is returned without re-execution.
    fn apply_primitive_step(&self, step: &ProofStep) -> Result<Self, ClickError> {
        match step {
            ProofStep::FoldResource(resource) => self.apply_primitive_fold(resource),
            ProofStep::UserTactic(_) => self.apply_execution_user_tactic(step.clone()),
            _ => self.apply_execution_statement_step_with_policy(
                step.clone(),
                StatementPrerequisitePolicy::Fast,
            ),
        }
    }

    /// Every requirement's Surface spelling must lower back to that
    /// requirement, so that the expanded `requires` entry matches it.
    fn debug_assert_spelling_relowers(
        &self,
        requirement: &UnresolvedRequirement,
        surface: &ClickProposition,
    ) {
        if !cfg!(debug_assertions) {
            return;
        }
        let lowered = self.lower_surface_goal(surface, "requirement spelling");
        debug_assert!(
            lowered
                .as_ref()
                .is_ok_and(|lowered| self.written_states_requirement(lowered, requirement)),
            "the spelling `{}` of requirement {:?} lowers to {:?}",
            crate::surface::printing::source_click_proposition(surface),
            requirement.proposition,
            lowered.map_err(|error| error.to_string())
        );
    }

    /// This Proof advanced by `stepped`'s checked step, recorded as one
    /// `StepProved` node so the obligation proofs expand with the step.
    fn step_proved_successor(
        &self,
        stepped: Self,
        step: ProofStep,
        proof: StepProofCertificate,
    ) -> Self {
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: stepped.state,
            node: ProofNode::step_child(
                &self.node,
                self.focused_branch_id(),
                Arc::new(ProofStep::StepProved {
                    step: Box::new(step),
                    proof,
                }),
            ),
        }
    }

    pub(super) fn execution_update_error(
        &self,
        operation: &str,
        error: ExecutionUpdateError,
    ) -> ClickError {
        match error {
            ExecutionUpdateError::NotFrontier => self.step_error(format!(
                "{operation} cannot advance C execution inside a proposition proof"
            )),
            ExecutionUpdateError::MissingExecution => {
                self.step_error("execution-frontier proof lost its semantic state")
            }
            ExecutionUpdateError::NotLoopBody => {
                self.step_error("`close_invariants` is only available in a loop-region proof")
            }
            ExecutionUpdateError::InvariantsAlreadyClosed => {
                self.step_error("the invariant bundle was closed more than once on one path")
            }
        }
    }

    /// The proof's facts with the body's memory effects and their store
    /// equations, as the loop's back edge reads them: the proof's own
    /// context extended by the effects, not a fold of every path fact.
    pub(in crate::surface::proof) fn back_edge_assumptions(
        &self,
        execution: &ExecutionProofState,
    ) -> PureFactContext {
        execution
            .core
            .effect_facts
            .iter()
            .map(|fact| fact.proposition().clone())
            .chain(crate::kernel::certified_store_equations(
                &execution.core.effect_facts,
            ))
            .fold(
                self.facts().pure_context(),
                PureFactContext::assume_proposition,
            )
    }

    /// Checks the heap, resource, and counted-population components at this
    /// loop-state join using the Proof-owned state and facts.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn check_loop_boundary(
        &self,
        loop_entry_state: &ExecutionState,
        loop_head_state: &ExecutionState,
        head_iterations: &crate::kernel::IntegerTerm,
        condition: Option<&ProgramExpression>,
        invariant_checks: &[LoopInvariantCheck],
        binders: &[crate::kernel::LoopBinder],
        structural_measure: Option<&str>,
        composite_resource_definitions: &[CompositeResourceDefinition],
    ) -> Result<LoopBoundary, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("loop state join requires an execution proof"));
        }
        self.require_execution_frontier("loop state join")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop state join lost its execution state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(self.step_error("loop state join requires a loop-region proof"));
        }
        let assumptions = self.back_edge_assumptions(execution);
        // The back edge binds the loop's names again before anything reads
        // them: whatever the body called the instance it ends holding, the
        // binder names it, and a body that ends with no instance at those
        // arguments fails here by name.
        let boundary_state = crate::kernel::loop_state_with_loop_binders_rebound(
            loop_head_state,
            &execution.core.state,
            binders,
            &assumptions,
        )
        .map_err(|message| self.step_error(format!("loop state join: {message}")))?;
        let invariant_obligations = crate::kernel::loop_invariant_obligations_at_back_edge(
            &boundary_state,
            loop_entry_state,
            invariant_checks,
            head_iterations,
            &assumptions,
        )
        .map_err(|message| self.step_error(format!("loop invariant classification: {message}")))?;
        let guard_assumptions = invariant_obligations
            .into_iter()
            .map(|obligation| obligation.proposition().clone())
            .fold(assumptions.clone(), PureFactContext::assume_proposition);
        let guard = match condition {
            Some(condition) => crate::kernel::classify_loop_condition(
                &boundary_state,
                condition,
                &guard_assumptions,
            )
            .map_err(|message| {
                self.step_error(format!("loop condition classification: {message}"))
            })?,
            None => crate::kernel::LoopConditionFeasibility::TrueOnly,
        };
        // Structural descent is owed only if another iteration can start.
        if guard.may_continue()
            && let Some(measure) = structural_measure
            && let Some(failure) = crate::kernel::loop_structural_descent_failure(
                loop_head_state,
                &boundary_state,
                binders,
                measure,
                composite_resource_definitions,
                &assumptions,
            )
        {
            return Err(self.step_error(format!("loop state join: {failure}")));
        }
        // Heap lifetime and resource ownership are compared against the head
        // the body actually started from. That is the loop entry context for
        // an ordinary loop, and the loop's own narrower resource context when
        // the loop declares `owns` or `views` clauses of its own. A binder's
        // model is what its invariants constrain, so the ownership comparison
        // sets it aside; the invariant obligations above checked it.
        let head_join = crate::kernel::loop_binder_state_components_match_at_back_edge(
            loop_head_state,
            &boundary_state,
            binders,
            &guard_assumptions,
            composite_resource_definitions,
        );
        let head_compatible = match head_join {
            Ok(()) => true,
            Err(message) if guard.may_continue() => {
                return Err(self.step_error(format!("loop state join: {message}")));
            }
            // The guard already establishes an exit. This comparison only
            // selects its representation; it does not classify control flow.
            Err(_) => false,
        };
        Ok(LoopBoundary {
            state: boundary_state,
            guard,
            head_compatible,
        })
    }

    /// Consume the complete prepared bundle without lowering or proof search.
    pub(in crate::surface::proof) fn validate_loop_invariant_bundle(
        &self,
        invariant_checks: &[LoopInvariantCheck],
        ranking_measures: &[crate::kernel::RankingComponent],
    ) -> Result<(), ClickError> {
        self.state
            .validate_checked_invariant_lowerings(invariant_checks, ranking_measures)
            .map_err(|message| self.step_error(message))
    }

    /// Record closure only after validating the exact retained evidence.
    ///
    /// The retained evidence is created by `retain_invariant_body`, which also
    /// requests the frontier's closure, so a validated bundle is always an
    /// already-closed one. Certification therefore adds no proof step of its
    /// own: the bundle's certificate step is the `close_invariants() by` node
    /// carrying the checked body, never a bare closure request that no
    /// explicit proof could spell.
    pub(in crate::surface::proof) fn certify_loop_invariant_bundle(
        &self,
        invariant_checks: &[LoopInvariantCheck],
        ranking_measures: &[crate::kernel::RankingComponent],
    ) -> Result<Self, ClickError> {
        self.validate_loop_invariant_bundle(invariant_checks, ranking_measures)?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop invariant closure lost its execution state"))?;
        if execution.core.region_invariants_close_requested {
            Ok(self.clone())
        } else {
            Err(self.step_error(
                "the loop invariant bundle carries checked body evidence without a closed frontier",
            ))
        }
    }

    /// Splits the focused branch preservation frontier under a proof-level `if`,
    /// introducing each arm's case assumption through the one shared
    /// case-assumption law, so lowered spellings, recorded surface
    /// propositions, and feasibility match the checked form exactly.
    /// Infeasible arms are omitted; the returned slots align `[then, else]`.
    /// Sibling arms stay separate — a preservation path never rejoins across
    /// the back edge — so no join consumes this split.
    pub(in crate::surface::proof) fn split_preservation_case(
        &self,
        condition: &ClickProposition,
        tactic_index: usize,
    ) -> Result<(Self, [Option<BranchId>; 2]), ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a preservation `if` requires an execution proof"));
        };
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("proof `if`")?;
        let mut base_execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        // A mid-execution case condition may name the current statement's
        // entry state before any step has crossed it; record it so the
        // form lowers, exactly as the checked `if` did.
        record_current_statement_entry(
            &base_execution.core.frontier,
            &mut base_execution.presentation.recorded_states,
            &base_execution.core.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            tactic_index,
            "if",
        )?;
        // A split that is this statement's own C `if` records the decision the
        // C program made, at the entry state where it was made, so a later
        // bundle closer can name it after the loop body has overwritten the
        // cells the condition read.
        let c_branch_condition =
            program_branch_condition_at_frontier(&base_execution, context, condition)?;
        let mut arms: [Option<(PureFactStore, ExecutionProofState, Vec<Proposition>)>; 2] =
            [None, None];
        let lowering_condition = self.substitute_fixed_state_locals_in_proposition(condition)?;
        for value in [true, false] {
            let mut arm_execution = base_execution.clone();
            if let Some(branch_condition) = &c_branch_condition {
                arm_execution
                    .presentation
                    .path_branch_premises
                    .push(if value {
                        branch_condition.clone()
                    } else {
                        negate_click_proposition(branch_condition)
                    });
            }
            let Some(added_fact) = introduce_proof_case_assumption(
                &mut arm_execution,
                &tactic_context,
                self.facts(),
                base_execution.core.has_structured_branch_history,
                condition,
                &lowering_condition,
                value,
            )?
            else {
                continue;
            };
            // Record where this proof-level case split sits in the path's
            // surface record, exactly as the checked form recorded it.
            if arm_execution.presentation.surface_record.blocker.is_none() {
                // The split sits after this path's own steps. The offset is
                // read back against the arm's `path_certificate()`, which
                // carries only the focused goal's lineage, so it is measured
                // the same way: a sibling arm stepped earlier in the same
                // derivation contributes steps to `certificate()` that this
                // path never took, and counting those puts the case past the
                // end of its own tactics.
                let tactic_offset = self.path_step_count()?;
                arm_execution
                    .presentation
                    .surface_record
                    .path_choices
                    .push(SurfacePathChoice {
                        occurrence: tactic_index,
                        selector: SurfacePathSelector::Proposition(condition.clone()),
                        value,
                        tactic_offset,
                    });
            }
            let added = added_fact.into_iter().collect::<Vec<_>>();
            let mut facts = self.facts().clone();
            for fact in &added {
                facts = facts.with_kernel_checked_fact(fact.clone());
            }
            arms[usize::from(!value)] = Some((facts, arm_execution, added));
        }
        match arms {
            [
                Some((then_facts, then_execution, then_added)),
                Some((else_facts, else_execution, else_added)),
            ] => {
                let split = self
                    .state
                    .publish_checked_frontier_split(
                        [(then_facts, then_execution), (else_facts, else_execution)],
                        [then_added, else_added],
                        Vec::new(),
                    )
                    .map_err(|error| self.execution_update_error("proof `if`", error))?;
                let (state, _, ids, _) = split.into_parts_with_facts();
                let successor = Self {
                    site: self.site.clone(),
                    context: self.context.clone(),
                    state,
                    node: ProofNode::marker(&self.node, self.focused_branch_id(), ids.to_vec()),
                };
                Ok((successor, [Some(ids[0]), Some(ids[1])]))
            }
            [then_arm, else_arm] => {
                let (value, (facts, execution, added)) = if let Some(arm) = then_arm {
                    (true, arm)
                } else if let Some(arm) = else_arm {
                    (false, arm)
                } else {
                    return Err(self.step_error(
                        "no feasible arm exists for this preservation `if` condition",
                    ));
                };
                let state = self
                    .state
                    .publish_checked_frontier_transition(facts, execution, added, Vec::new())
                    .map_err(|error| self.execution_update_error("proof `if`", error))?;
                let successor = Self {
                    site: self.site.clone(),
                    context: self.context.clone(),
                    state,
                    node: self.node.clone(),
                };
                let mut ids = [None, None];
                ids[usize::from(!value)] = Some(successor.focused_branch_id());
                Ok((successor, ids))
            }
        }
    }

    /// Records where the checked `close_invariants` tactic sat, so the
    /// kernel re-derivation its caller performs at the bundle check can be
    /// timed against that tactic's identity. Cursor metadata only.
    pub(in crate::surface::proof) fn record_invariant_closer(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`close_invariants`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let statement_index = execution.core.frontier.next_statement_index;
        let (proof, ()) = self.clone().edit_execution_presentation(|presentation| {
            presentation.invariant_closer_step = Some(InvariantCloserStep {
                tactic_index,
                source_index,
                statement_index,
            });
        })?;
        let state = proof.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(proof.with_kernel_state(state))
    }

    /// Records a region-level `solve` for the loop-invariant bundle. The
    /// tactic's semantic content is the bundle closer certified at the
    /// typed boundary, so only its identity is recorded here — cursor
    /// metadata for expansion capture and timing attribution, never a
    /// semantic transition.
    pub(in crate::surface::proof) fn defer_region_solve(
        &self,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("`solve`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.core.frontier.region != ExecutionRegionKind::LoopBody {
            return Err(
                self.step_error("a region `solve` is only available in a loop-region proof")
            );
        }
        let (proof, ()) = self.clone().edit_execution_presentation(|presentation| {
            presentation.region_solve = Some((tactic_index, source_index));
        })?;
        let state = proof.state.with_fact_deltas(Vec::new(), Vec::new());
        Ok(proof.with_kernel_state(state))
    }

    /// Applies a frontier-local `loop` tactic as one checked operation on
    /// the focused branch execution frontier: the loop's phases verify through the
    /// shared loop-planning machinery, the certified loop rule replaces the
    /// `while` statement in the frontier's own statement tree, and the
    /// derived exit facts join this goal's context. The surface record and
    /// expansion capture ride the transitional cursor exactly as the
    /// checked form recorded them.
    pub(in crate::surface::proof) fn apply_frontier_local_loop(
        &self,
        mut expansion_capture: Option<&mut ExpansionCapture>,
        loop_clause: &StructuralClause,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`loop` requires an execution-frontier proof"));
        };
        let read_checkpoint = crate::surface::proof_trace::enabled_for(self.claim_label())
            .then(|| {
                self.focused_branch()
                    .map(|branch| branch.state.facts.assumptions().read_equality_checkpoint())
            })
            .flatten();
        let tactic_context = context.with_tactic_index(tactic_index);
        self.require_execution_frontier("`loop`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let source_facts = self.facts().clone();
        let mut facts = PureFactList::from_store(&source_facts);
        let capture_this_tactic = begin_tactic_expansion_capture(
            expansion_capture.as_deref_mut(),
            source_index,
            &execution.presentation.expansion,
            context.constants.proof_site.as_ref(),
        );
        let _timing = TacticTiming::new(
            context.claim_label,
            tactic_index,
            source_index,
            &ProofTactic::Loop(loop_clause.clone()),
            execution.core.frontier.next_statement_index,
        );
        // The loop clauses are written inside whatever proof scope reached
        // this frontier; the re-annotation resolves that scope's locals
        // before lowering them, as a `have` goal at this point would.
        let proof_locals = self.proof_local_values();
        let trace_lineage = self.trace_lineage(context.claim_label);
        let (expanded_loop, added) =
            crate::surface::proof_trace::with_loop_parent_lineage(trace_lineage, || {
                execute_frontier_local_loop(
                    expansion_capture.as_deref_mut(),
                    loop_clause,
                    &proof_locals,
                    self.facts(),
                    &mut execution,
                    &tactic_context,
                    &mut facts,
                    source_index,
                )
            })?;
        if capture_this_tactic {
            // The tactic's expansion is the expanded loop itself.
            let expansion = ProofCertificateBuilder {
                steps: ProofCertificate::from_proof_tactics(std::slice::from_ref(
                    &ProofTactic::Loop(expanded_loop.clone()),
                ))
                .expect("an expanded loop is one proof step")
                .steps()
                .to_vec(),
                ..ProofCertificateBuilder::default()
            };
            finish_tactic_expansion_capture(expansion_capture, &expansion, false);
        }
        let mut proof_facts = source_facts;
        for fact in &added {
            proof_facts = proof_facts.with_kernel_checked_fact(fact.clone());
        }
        // Retain the expanded loop clause as checked evidence so
        // whole-claim expansion serializes it without consulting the
        // transitional builder record.
        let loop_step = ProofCertificate::from_proof_tactics(std::slice::from_ref(
            &ProofTactic::Loop(expanded_loop),
        ))
        .map_err(|error| {
            self.step_error(format!(
                "`loop` produced an invalid expanded clause: {error}"
            ))
        })?
        .steps()[0]
            .clone();
        let state = self
            .state
            .publish_checked_frontier_transition(proof_facts, execution, added, Vec::new())
            .map_err(|error| self.execution_update_error("`loop`", error))?;
        let next = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(self.node.clone()),
                step: Some(Arc::new(loop_step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
                split_branches: Vec::new(),
            }),
        };
        if crate::surface::proof_trace::enabled_for(self.claim_label()) {
            // The loop's exported delta is the evidence available to its
            // continuation, including the exit disjunction. Do not truncate
            // that delta before it reaches the shared fact renderer.
            self.record_checked_trace_step(
                &next,
                "loop",
                None,
                None,
                usize::MAX,
                read_checkpoint.as_ref(),
                Vec::new(),
            );
        }
        Ok(next)
    }
}

/// The body of the one `have` a proof of a step obligation retained.
fn retained_have_body(certificate: &ProofCertificate) -> Result<ProofCertificate, ClickError> {
    certificate
        .steps()
        .iter()
        .rev()
        .find_map(|step| match step {
            ProofStep::Have { proof, .. } => Some(proof.as_ref().clone()),
            _ => None,
        })
        .ok_or_else(|| ClickError::new("a step obligation proof retained no `have`"))
}

/// Requirements up to the comparison used by written obligation proofs, in
/// the order first met. In particular, different closed true comparisons
/// must not produce entries that replay matches to the same obligation.
fn distinct_requirements(recorded: Vec<UnresolvedRequirement>) -> Vec<UnresolvedRequirement> {
    let mut distinct: Vec<UnresolvedRequirement> = Vec::new();
    for requirement in recorded {
        if !distinct.iter().any(|seen| {
            super::super::smart_closures::propositions_match_after_canonical_loads(
                &seen.proposition,
                &requirement.proposition,
            )
        }) {
            distinct.push(requirement);
        }
    }
    distinct
}

#[test]
fn requirement_deduplication_uses_replay_truth_and_polarity() {
    let requirement = |left: u32, right: u32| UnresolvedRequirement {
        proposition: Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(left.into()),
                right: Box::new(right.into()),
            },
            true,
        ),
        context: None,
        introductions: Default::default(),
        call_site: None,
        assertion_condition: None,
        surface: None,
    };
    let first = requirement(0, 0);
    let false_bound = requirement(2, 1);
    let distinct =
        distinct_requirements(vec![first.clone(), requirement(0, 1), false_bound.clone()]);
    assert_eq!(distinct, vec![first, false_bound]);
}

thread_local! {
    static IMPLICIT_SOLVE_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(in crate::surface::proof) fn implicit_solve_disabled() -> bool {
    IMPLICIT_SOLVE_DISABLED.with(std::cell::Cell::get)
        || super::super::implicit_solve_scope::selected_claim_is_strict()
}

/// Runs `operation` with the implicit `solve` off: a step gets only its fast
/// path and its written obligation proofs, with no search, so an obligation
/// nothing written proves is refused with its structured requirement.
/// The implicit tail is off with it: a script that leaves C to run, or a
/// goal open, at its end is refused instead of finished by search. This is
/// unconditional across all proof units. Audit uses
/// [`crate::surface::without_implicit_solve_for_claim`] when untouched proof
/// units are also visited during targeted verification.
pub fn without_implicit_solve<R>(operation: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            IMPLICIT_SOLVE_DISABLED.with(|disabled| disabled.set(self.0));
        }
    }
    let _restore = Restore(IMPLICIT_SOLVE_DISABLED.with(|disabled| disabled.replace(true)));
    operation()
}

/// The call a `step(callee, { ... })` runs at the frontier: its execution
/// name and argument expressions.
struct FrontierCall {
    callee: String,
    arguments: Vec<ProgramExpression>,
}

/// The descent member of a ranked loop as its `decreases` clause writes it:
/// `m < at(<iteration entry>, m)` for one component, and for a tuple the
/// right-nested disjunction over pivots the kernel builds, each pivot strictly
/// smaller with every earlier component tied, `m == at(<iteration entry>, m)`.
/// The member reads its `pre` values at the iteration entry, as an `ensures`
/// reads them through `old`, so it is spelled the way its author would write
/// it, not reconstructed from the lowered goal.
fn ranking_descent_surface(bundle: &InvariantBodyContext) -> Option<ClickProposition> {
    let selector = bundle.iteration_entry_selector.as_ref()?;
    let components = &bundle.ranking_surfaces;
    if components.is_empty() || components.len() != bundle.ranking_measures.len() {
        return None;
    }
    let compare = |component: &ContractExpression, operator: ComparisonOperator| {
        ClickProposition::Comparison {
            left: component.clone(),
            operator,
            right: ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(component.clone()),
            },
        }
    };
    let arm = |pivot: usize| {
        (0..pivot).rev().fold(
            compare(&components[pivot], ComparisonOperator::LessThan),
            |rest, index| {
                ClickProposition::And(
                    Box::new(compare(&components[index], ComparisonOperator::Equal)),
                    Box::new(rest),
                )
            },
        )
    };
    (0..components.len()).rev().fold(None, |rest, pivot| {
        Some(match rest {
            None => arm(pivot),
            Some(rest) => ClickProposition::Or(Box::new(arm(pivot)), Box::new(rest)),
        })
    })
}

thread_local! {
    /// Set while one invariant bundle member is proved in its own `have`, so
    /// that proof closes the member itself rather than wrapping it again.
    static IN_BUNDLE_MEMBER_HAVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[path = "../driver/obligations.rs"]
mod driver;

mod search;

/// Where the statement at the frontier leaves the result a `step` binds.
enum FrontierResult {
    /// The local it assigns.
    Local(crate::kernel::BindingName),
    /// The typed result the step retained.
    Retained(u32),
}
