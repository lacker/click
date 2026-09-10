//! Contextual Surface Click lowering for checked proof operations.

use super::pure_theorems::{
    lower_pure_theorem_proposition, lower_pure_theorem_proposition_with_algebraic_values,
    lower_pure_theorem_proposition_with_integer_values,
};
use super::*;

pub(super) fn proposition_uses_integer(
    proposition: &ClickProposition,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            expression_uses_integer(left, integer_values)
                || expression_uses_integer(right, integer_values)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_uses_integer(left, integer_values)
                || proposition_uses_integer(right, integer_values)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
        | ClickProposition::RangeAll { body, .. }
        | ClickProposition::RangeAny { body, .. }
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => proposition_uses_integer(body, integer_values),
        _ => false,
    }
}

fn expression_uses_integer(
    expression: &ContractExpression,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
) -> bool {
    match expression {
        ContractExpression::Binding(name) => integer_values.get(name).is_some(),
        ContractExpression::Negate(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::Index(_, inner) => expression_uses_integer(inner, integer_values),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            expression_uses_integer(left, integer_values)
                || expression_uses_integer(right, integer_values)
        }
        ContractExpression::Let {
            click_type,
            value,
            body,
            ..
        } => {
            matches!(click_type, Some(ClickType::Integer))
                || expression_uses_integer(value, integer_values)
                || expression_uses_integer(body, integer_values)
        }
        _ => false,
    }
}

impl<'a> Proof<'a> {
    pub(in crate::surface::proof) fn lower_surface_proposition(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                if let Some(recorded) = context
                    .theorem_context
                    .surface_requirements
                    .available_kernel_matching(surface, |kernel| self.facts().contains(kernel))
                {
                    return Ok(recorded.clone());
                }
                if proposition_uses_integer(surface, &context.theorem_context.integer_values) {
                    lower_pure_theorem_proposition_with_integer_values(
                        context.claim_label,
                        surface,
                        &context.theorem_context.values,
                        &context.theorem_context.integer_values,
                        &context.theorem_context.array_refs,
                        &context.theorem_context.memory,
                        context.predicate_environment,
                        context.click_function_environment,
                    )
                } else {
                    lower_pure_theorem_proposition_with_algebraic_values(
                        context.claim_label,
                        surface,
                        &context.theorem_context.values,
                        &context.theorem_context.array_refs,
                        context
                            .structural_induction_setup
                            .as_ref()
                            .map(|setup| &setup.algebraic_values)
                            .unwrap_or(&BTreeMap::new()),
                        &context.theorem_context.memory,
                        context.predicate_environment,
                        context.click_function_environment,
                    )
                }
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::FixedState(context) => {
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                if !proposition_contains_old_expression(&surface)
                    && let Some(recorded) = context
                        .surface_propositions
                        .available_kernel(&surface, context.lowering_context.as_ref())
                {
                    return Ok(recorded.clone());
                }
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            // A judgment carrying outcome proof data lowers result-aware:
            // `result` and outcome-anchored forms resolve against the
            // outcome's own state, recorded lowerings, and return value.
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                // An available historical fact is not the meaning of a
                // current-state expression with the same spelling: an entry
                // resource fact such as `cell[0] == 8` survives the store of 7,
                // and reusing it for a proof `if` condition would make the
                // condition and its negation lower against different states.
                // Resolve current-state expressions against the outcome's own
                // snapshot. Fully anchored spellings are different: their
                // recorded identity deliberately names that historical fact.
                let explicitly_anchored = match &surface {
                    ClickProposition::At { .. } => true,
                    ClickProposition::PredicateCall { arguments, .. } => {
                        matches!(arguments.first(), Some(ContractExpression::At { selector, .. })
                            if arguments.iter().all(|argument| matches!(argument,
                                ContractExpression::At { selector: other, .. } if other == selector)))
                    }
                    _ => false,
                };
                if explicitly_anchored
                    && !proposition_contains_old_expression(&surface)
                    && let Some(recorded) = view
                        .surface_propositions
                        .available_kernel_matching(&surface, |kernel| self.facts().contains(kernel))
                {
                    return Ok(recorded.clone());
                }
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.recorded_snapshots,
                    view.predicate_environment,
                    view.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::Execution(context) => {
                let execution = self.execution().ok_or_else(|| {
                    self.step_error("execution proposition proof lost its semantic frontier")
                })?;
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                let pre_state =
                    context.old_reference_state(&execution.core.frontier, &execution.core.state);
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parsed_function.parameters(),
                    context.arguments,
                    pre_state,
                    &execution.core.state,
                    None,
                    &execution.presentation.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
        }
    }

    /// Lowers a surface proposition against this Proof's actual symbolic state,
    /// without accepting a historical Surface-to-kernel index entry as a
    /// substitute for an in-scope form.
    ///
    /// The independent certificate validator may use that index to recognize an
    /// exact fact.
    /// Smart theorem selection additionally needs arguments that can be
    /// lowered when the retained `apply` step runs. In particular, a local
    /// that has left scope must be written through `at(...)` rather than
    /// merely associated with an indexed historical fact.
    pub(in crate::surface::proof) fn lower_surface_proposition_direct(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => lower_pure_theorem_proposition(
                context.claim_label,
                surface,
                &context.theorem_context.values,
                &context.theorem_context.array_refs,
                &context.theorem_context.memory,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                self.step_error(format!("could not lower {description}: {message}"))
            }),
            ProofContext::FixedState(context) => {
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.recorded_snapshots,
                    view.predicate_environment,
                    view.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::Execution(context) => {
                let execution = self.execution().ok_or_else(|| {
                    self.step_error("execution proposition proof lost its semantic frontier")
                })?;
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                let pre_state =
                    context.old_reference_state(&execution.core.frontier, &execution.core.state);
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parsed_function.parameters(),
                    context.arguments,
                    pre_state,
                    &execution.core.state,
                    None,
                    &execution.presentation.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
        }
    }

    /// Lowers a newly stated proof goal against the current symbolic state.
    ///
    /// Fact references may deliberately resolve through a recorded surface
    /// form, but a new goal may not: the same form can name facts
    /// retained from an older snapshot. Selecting such a fact here would let
    /// `have P by assumption` check one kernel proposition and serialize a
    /// surface `P` that independently lowers to another.
    pub(super) fn lower_surface_goal(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.lower_surface_proposition(surface, description),
            ProofContext::FixedState(context) => {
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.recorded_snapshots,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            // A judgment stated at a function outcome lowers strictly at
            // that outcome: like the fixed-state arm above, this deliberately
            // skips the recorded-lowering shortcut so a newly stated goal
            // cannot borrow a same-written fact's older snapshot anchoring.
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                lower_fixed_state_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.recorded_snapshots,
                    view.predicate_environment,
                    view.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::Execution(_) => self.lower_surface_proposition(surface, description),
        }
    }

    /// Materializes only proof-local substitutions named by this explicit
    /// surface input. Work is proportional to the input expression and each
    /// selected name is an indexed persistent-map lookup; unrelated choices
    /// are neither scanned nor cloned.
    pub(super) fn fixed_state_local_substitutions(
        &self,
        names: impl IntoIterator<Item = String>,
    ) -> BTreeMap<String, ContractExpression> {
        let surface_bindings = self
            .proposition_obligation()
            .map(|goal| &goal.surface_bindings);
        names
            .into_iter()
            .filter_map(|name| {
                surface_bindings
                    .and_then(|bindings| bindings.get(&name))
                    .or_else(|| self.local_binding(&name))
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect()
    }

    pub(super) fn substitute_fixed_state_locals_in_proposition(
        &self,
        proposition: &ClickProposition,
    ) -> Result<ClickProposition, ClickError> {
        let mut names = BTreeSet::new();
        collect_click_proposition_referenced_names(proposition, &mut names);
        let substitutions = self.fixed_state_local_substitutions(names);
        if substitutions.is_empty() {
            return Ok(proposition.clone());
        }
        substitute_click_proposition(proposition, &substitutions).map_err(|message| {
            self.step_error(format!("could not substitute proof locals: {message}"))
        })
    }

    /// Substitutes only logical binders introduced while refining this
    /// proposition goal. General proof locals participate in source-level
    /// selection elsewhere; eagerly substituting them into every transport
    /// candidate turns prompt form rejection into expensive semantic
    /// alias search.
    pub(super) fn substitute_goal_surface_bindings_in_proposition(
        &self,
        proposition: &ClickProposition,
    ) -> Result<ClickProposition, ClickError> {
        let Some(goal) = self.proposition_obligation() else {
            return Ok(proposition.clone());
        };
        let mut names = BTreeSet::new();
        collect_click_proposition_referenced_names(proposition, &mut names);
        let substitutions = names
            .into_iter()
            .filter_map(|name| {
                goal.surface_bindings
                    .get(&name)
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect::<BTreeMap<_, _>>();
        if substitutions.is_empty() {
            return Ok(proposition.clone());
        }
        substitute_click_proposition(proposition, &substitutions).map_err(|message| {
            self.step_error(format!(
                "could not substitute proposition-goal binders: {message}"
            ))
        })
    }

    pub(super) fn substitute_goal_surface_bindings_in_expression(
        &self,
        expression: &ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let Some(goal) = self.proposition_obligation() else {
            return Ok(expression.clone());
        };
        let substitutions = contract_expression_referenced_names(expression)
            .into_iter()
            .filter_map(|name| {
                goal.surface_bindings
                    .get(&name)
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect::<BTreeMap<_, _>>();
        if substitutions.is_empty() {
            return Ok(expression.clone());
        }
        substitute_contract_expression(expression, &substitutions).map_err(|message| {
            self.step_error(format!(
                "could not substitute expression-goal binders: {message}"
            ))
        })
    }

    pub(super) fn substitute_fixed_state_locals_in_expression(
        &self,
        expression: &ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let names = contract_expression_referenced_names(expression);
        let substitutions = self.fixed_state_local_substitutions(names);
        if substitutions.is_empty() {
            return Ok(expression.clone());
        }
        substitute_contract_expression(expression, &substitutions).map_err(|message| {
            self.step_error(format!("could not substitute proof locals: {message}"))
        })
    }
}
