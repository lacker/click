//! Contextual Surface Click lowering for checked proof operations.

use super::pure_theorems::lower_pure_theorem_proposition_with_algebraic_and_integer_values;
use super::*;

fn promote_integer_expression(
    expression: &ContractExpression,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    surface_bindings: &crate::persistent::PersistentMap<String, ContractExpression>,
) -> ContractExpression {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name))
            if integer_values.get(name).is_some() && surface_bindings.get(name).is_none() =>
        {
            ContractExpression::Binding(name.clone())
        }
        ContractExpression::Negate(inner) => ContractExpression::Negate(Box::new(
            promote_integer_expression(inner, integer_values, surface_bindings),
        )),
        ContractExpression::Add(left, right) => ContractExpression::Add(
            Box::new(promote_integer_expression(
                left,
                integer_values,
                surface_bindings,
            )),
            Box::new(promote_integer_expression(
                right,
                integer_values,
                surface_bindings,
            )),
        ),
        ContractExpression::Subtract(left, right) => ContractExpression::Subtract(
            Box::new(promote_integer_expression(
                left,
                integer_values,
                surface_bindings,
            )),
            Box::new(promote_integer_expression(
                right,
                integer_values,
                surface_bindings,
            )),
        ),
        ContractExpression::Multiply(left, right) => ContractExpression::Multiply(
            Box::new(promote_integer_expression(
                left,
                integer_values,
                surface_bindings,
            )),
            Box::new(promote_integer_expression(
                right,
                integer_values,
                surface_bindings,
            )),
        ),
        _ => expression.clone(),
    }
}

pub(super) fn promote_integer_comparison(
    surface: &ClickProposition,
    integer_values: &crate::persistent::PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    surface_bindings: &crate::persistent::PersistentMap<String, ContractExpression>,
) -> ClickProposition {
    match surface {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => ClickProposition::Comparison {
            left: promote_integer_expression(left, integer_values, surface_bindings),
            operator: *operator,
            right: promote_integer_expression(right, integer_values, surface_bindings),
        },
        ClickProposition::And(left, right) => ClickProposition::And(
            Box::new(promote_integer_comparison(
                left,
                integer_values,
                surface_bindings,
            )),
            Box::new(promote_integer_comparison(
                right,
                integer_values,
                surface_bindings,
            )),
        ),
        ClickProposition::Or(left, right) => ClickProposition::Or(
            Box::new(promote_integer_comparison(
                left,
                integer_values,
                surface_bindings,
            )),
            Box::new(promote_integer_comparison(
                right,
                integer_values,
                surface_bindings,
            )),
        ),
        ClickProposition::Implies(left, right) => ClickProposition::Implies(
            Box::new(promote_integer_comparison(
                left,
                integer_values,
                surface_bindings,
            )),
            Box::new(promote_integer_comparison(
                right,
                integer_values,
                surface_bindings,
            )),
        ),
        ClickProposition::Not(body) => ClickProposition::Not(Box::new(promote_integer_comparison(
            body,
            integer_values,
            surface_bindings,
        ))),
        ClickProposition::At {
            selector,
            proposition,
        } => ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(promote_integer_comparison(
                proposition,
                integer_values,
                surface_bindings,
            )),
        },
        _ => surface.clone(),
    }
}

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
                // A pure goal's universal binders are named only by this
                // goal's retained bindings; the theorem's parameter values
                // do not mention them.
                let surface = self.substitute_goal_surface_bindings_in_proposition(surface)?;
                let empty_algebraic_values = BTreeMap::new();
                lower_pure_theorem_proposition_with_algebraic_and_integer_values(
                    context.claim_label,
                    &surface,
                    &context.theorem_context.values,
                    &context.theorem_context.array_refs,
                    context
                        .structural_induction_setup
                        .as_ref()
                        .map(|setup| &setup.algebraic_values)
                        .unwrap_or(&empty_algebraic_values),
                    &context.theorem_context.integer_values,
                    &context.theorem_context.memory,
                    context.predicate_environment,
                    context.click_function_environment,
                )
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
            ProofContext::Pure(context) => {
                let surface = self.substitute_goal_surface_bindings_in_proposition(surface)?;
                let empty_algebraic_values = BTreeMap::new();
                lower_pure_theorem_proposition_with_algebraic_and_integer_values(
                    context.claim_label,
                    &surface,
                    &context.theorem_context.values,
                    &context.theorem_context.array_refs,
                    context
                        .structural_induction_setup
                        .as_ref()
                        .map(|setup| &setup.algebraic_values)
                        .unwrap_or(&empty_algebraic_values),
                    &context.theorem_context.integer_values,
                    &context.theorem_context.memory,
                    context.predicate_environment,
                    context.click_function_environment,
                )
            }
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
        self.lower_surface_goal_recording_introductions(surface, description)
            .map(|(proposition, _)| proposition)
    }

    /// [`Self::lower_surface_goal`], also returning the head chain the
    /// kernel lowering recorded for the goal it produced, when this context
    /// lowered the goal itself. `None` means no lowering provenance was
    /// recorded for this goal: the proposition came from a recorded
    /// correspondence rather than from a lowering performed here.
    pub(super) fn lower_surface_goal_recording_introductions(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<(Proposition, Option<crate::kernel::LoweringIntroductions>), ClickError> {
        match self.context.as_ref() {
            // A pure goal may resolve through a recorded requirement
            // correspondence, which carries no lowering of its own; only a
            // lowering performed here records a head chain.
            ProofContext::Pure(context) => {
                if let Some(recorded) = context
                    .theorem_context
                    .surface_requirements
                    .available_kernel_matching(surface, |kernel| self.facts().contains(kernel))
                {
                    return Ok((recorded.clone(), None));
                }
                let surface = self.substitute_goal_surface_bindings_in_proposition(surface)?;
                let empty_algebraic_values = BTreeMap::new();
                let mut integer_values = context.theorem_context.integer_values.clone();
                for (name, value) in self.local_integer_values().iter() {
                    integer_values = integer_values.with_inserted(name.clone(), value.clone());
                }
                let surface = self.proposition_obligation().map_or_else(
                    || surface.clone(),
                    |goal| {
                        promote_integer_comparison(
                            &surface,
                            &integer_values,
                            &goal.surface_bindings,
                        )
                    },
                );
                super::pure_theorems::lower_pure_theorem_proposition_recording_introductions(
                    context.claim_label,
                    &surface,
                    &context.theorem_context.values,
                    &context.theorem_context.array_refs,
                    context
                        .structural_induction_setup
                        .as_ref()
                        .map(|setup| &setup.algebraic_values)
                        .unwrap_or(&empty_algebraic_values),
                    &integer_values,
                    &context.theorem_context.memory,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map(|(proposition, introductions)| (proposition, Some(introductions)))
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::FixedState(context) => {
                let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
                lower_fixed_state_proposition_with_assumptions_recording_introductions(
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
                .map(|(proposition, introductions)| (proposition, Some(introductions)))
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
                lower_fixed_state_proposition_with_assumptions_recording_introductions(
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
                .map(|(proposition, introductions)| (proposition, Some(introductions)))
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            // A goal stated at an execution frontier resolves through the
            // shared proposition lowering, which may answer from a recorded
            // correspondence; that route records no head chain of its own.
            ProofContext::Execution(_) => self
                .lower_surface_proposition(surface, description)
                .map(|proposition| (proposition, None)),
        }
    }

    /// Lowers a Surface proposition a proof step cites as a fact of the
    /// focused goal.
    ///
    /// Two things separate a citation from a newly stated goal. First, an
    /// antecedent that one of this goal's own introductions added is
    /// retained with the exact kernel fact the kernel added; re-lowering it
    /// here would run under the fact context that introduction changed,
    /// which produces no path at all for an antecedent no state satisfies.
    /// Second, a citation may name a universal binder this goal introduced,
    /// which resolves through the retained binding rather than through an
    /// independently chosen value.
    pub(in crate::surface::proof) fn lower_cited_surface_proposition(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        if let Some(goal) = self.proposition_obligation()
            && let Some(retained) =
                retained_introduced_antecedent(&goal.introduced_antecedents, surface)
        {
            return Ok(retained.clone());
        }
        let surface = self.substitute_goal_surface_bindings_in_proposition(surface)?;
        if let Some(goal) = self.proposition_obligation()
            && let Some(retained) =
                retained_introduced_antecedent(&goal.introduced_antecedents, &surface)
        {
            return Ok(retained.clone());
        }
        self.lower_surface_proposition(&surface, description)
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
