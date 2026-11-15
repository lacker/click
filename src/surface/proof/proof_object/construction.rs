//! Constructors for pure, fixed-state, and surface proof goals.

use super::*;

impl<'a> Proof<'a> {
    /// Attaches the head chain the kernel recorded while lowering this
    /// root goal.
    ///
    /// A goal constructor receives an already lowered proposition, so the
    /// record arrives beside it. Installing it is presentation only: the
    /// checked proposition, facts, and provenance node are unchanged, and
    /// `None` (no lowering performed for this goal) leaves the goal in the
    /// unrecorded state where introductions refine the written form
    /// structurally.
    pub(in crate::surface::proof) fn with_recorded_goal_introductions(
        &self,
        introductions: Option<crate::kernel::LoweringIntroductions>,
    ) -> Self {
        let Some(introductions) = introductions else {
            return self.clone();
        };
        let Some(state) = self
            .state
            .with_focused_proposition_presentation(|presentation| PropositionPresentation {
                introductions: GoalIntroductions::from_lowering(Some(introductions)),
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

    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_contract_refinement_goal(
        claim_label: &'a str,
        goal: Proposition,
        surface_goal: ClickProposition,
        parameter_binding: ParameterBinding<'a>,
        entry: &'a ExecutionState,
        post: &'a ExecutionState,
        result: Option<&'a ProgramValue>,
        retained_states: &'a RecordedStates,
        surfaces: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorems: &'a TheoremEnvironment,
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            0,
            FixedStateFacts::Slice(&[]),
            |state| {
                OpenBranch::new(
                    Obligation::Proposition(PropositionObligation::new(
                        goal,
                        PropositionPresentation {
                            surface: Some(Arc::new(surface_goal)),
                            generated_surface: true,
                            ..PropositionPresentation::default()
                        },
                    )),
                    state,
                )
            },
            parameter_binding,
            FixedStateFrame::new(entry, post, result, retained_states),
            None,
            surfaces,
            spec_definitions,
            theorems,
            &[],
            &[],
            &[],
            None,
        )
    }
    /// Reattributes subsequent execution-structure diagnostics to the source
    /// tactic that owns them without changing proof state or provenance.
    ///
    /// Simple steps carry their own origins. Structural operations span
    /// several checked transitions, so a long-lived function Proof updates
    /// this cursor metadata before entering each top-level structure.
    pub(in crate::surface::proof) fn with_execution_tactic_index(
        &self,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("execution tactic attribution requires an execution proof"));
        };
        if context.tactic_index == tactic_index {
            return Ok(self.clone());
        }
        Ok(Self {
            site: self.site.clone(),
            context: Arc::new(ProofContext::Execution(
                context.with_tactic_index(tactic_index),
            )),
            state: self.state.clone(),
            node: self.node.clone(),
        })
    }

    /// Names `step_tactic_name` as the source tactic of the statement steps
    /// checked from this proof, without changing proof state or provenance:
    /// the implicit tail, advancing statement by statement, is refused as
    /// `step()`, the step that refused.
    pub(in crate::surface::proof) fn with_execution_step_tactic_name(
        &self,
        step_tactic_name: &'static str,
    ) -> Self {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return self.clone();
        };
        if context.step_tactic_name == step_tactic_name {
            return self.clone();
        }
        Self {
            site: self.site.clone(),
            context: Arc::new(ProofContext::Execution(
                context.with_step_tactic_name(step_tactic_name),
            )),
            state: self.state.clone(),
            node: self.node.clone(),
        }
    }

    /// This proof under `ancestor`'s exact context: undoes
    /// [`Self::with_execution_step_tactic_name`] once the steps it named have
    /// run, so certificate checkpoints taken against `ancestor` still apply.
    pub(in crate::surface::proof) fn with_context_of(self, ancestor: &Self) -> Self {
        Self {
            context: ancestor.context.clone(),
            ..self
        }
    }

    /// Restores an ancestor's source site and execution diagnostic context
    /// after a nested structural operation. The descendant check is provenance-based;
    /// this changes no goals, facts, execution state, or proof nodes.
    pub(in crate::surface::proof) fn restore_execution_tactic_attribution(
        &self,
        ancestor: &Self,
    ) -> Result<Self, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_))
            || !matches!(ancestor.context.as_ref(), ProofContext::Execution(_))
        {
            return Err(self.step_error(
                "execution tactic attribution can only be restored on execution proofs",
            ));
        }
        let mut node = Some(self.node.clone());
        let mut is_descendant = false;
        while let Some(current) = node {
            if Arc::ptr_eq(&current, &ancestor.node) {
                is_descendant = true;
                break;
            }
            node = current.parent.clone();
        }
        if !is_descendant {
            return Err(self
                .step_error("execution tactic attribution can only be restored from an ancestor"));
        }
        Ok(Self {
            site: ancestor.site.clone(),
            context: ancestor.context.clone(),
            state: self.state.clone(),
            node: self.node.clone(),
        })
    }

    #[cfg(test)]
    pub(in crate::surface::proof) fn for_pure_goal(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        theorem_context: &'a PureTheoremContext,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        Self::for_pure_goal_with_surface(
            claim_label,
            requires,
            goal,
            None,
            theorem_context,
            spec_definitions,
            theorem_environment,
        )
    }

    pub(in crate::surface::proof) fn for_pure_surface_goal(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        theorem_context: &'a PureTheoremContext,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        Self::for_pure_goal_with_surface(
            claim_label,
            requires,
            goal,
            Some(surface_goal),
            theorem_context,
            spec_definitions,
            theorem_environment,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_pure_surface_goal_with_induction(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        theorem_context: &'a PureTheoremContext,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        induction_setup: PureInductionSetup,
    ) -> Self {
        Self::for_pure_goal_with_surface_and_induction(
            claim_label,
            requires,
            goal,
            Some(surface_goal),
            theorem_context,
            spec_definitions,
            theorem_environment,
            Some(induction_setup),
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_pure_surface_goal_with_structural_induction(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        theorem_context: &'a PureTheoremContext,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        structural_induction_setup: PureStructuralInductionBranchSetup,
    ) -> Self {
        Self::for_pure_goal_with_surface_and_induction(
            claim_label,
            requires,
            goal,
            Some(surface_goal),
            theorem_context,
            spec_definitions,
            theorem_environment,
            None,
            Some(structural_induction_setup),
        )
    }

    pub(super) fn for_pure_goal_with_surface(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
        theorem_context: &'a PureTheoremContext,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        Self::for_pure_goal_with_surface_and_induction(
            claim_label,
            requires,
            goal,
            surface_goal,
            theorem_context,
            spec_definitions,
            theorem_environment,
            None,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn for_pure_goal_with_surface_and_induction(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
        theorem_context: &'a PureTheoremContext,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        induction_setup: Option<PureInductionSetup>,
        structural_induction_setup: Option<PureStructuralInductionBranchSetup>,
    ) -> Self {
        let mut ambient_variables = std::collections::BTreeSet::new();
        let mut source_state = ExecutionState::new().with_memory(theorem_context.memory.clone());
        for (name, value) in &theorem_context.values {
            crate::kernel::collect_program_value_bitvector_variables(value, &mut ambient_variables);
            source_state = source_state.with_local(name.clone(), value.clone());
        }
        for (_, value) in theorem_context.integer_values.iter() {
            crate::kernel::collect_spec_integer_variables(value, &mut ambient_variables);
        }
        ambient_variables.extend(crate::kernel::proposition_variables(&goal));
        if let Some(setup) = &structural_induction_setup {
            for value in setup.algebraic_values.values() {
                crate::kernel::collect_spec_algebraic_expression_bitvector_variables(
                    value,
                    &mut ambient_variables,
                );
            }
        }
        let facts = ProofFacts::from_ordered(requires).with_reserved_variables(ambient_variables);
        Self {
            site: ProofStepSite::default(),
            context: Arc::new(ProofContext::Pure(PureProofContext {
                claim_label,
                theorem_context,
                source_state,
                source_names: theorem_context.diagnostic_names.iter().cloned().collect(),
                spec_definitions,
                theorem_environment,
                induction_setup,
                structural_induction_setup,
            })),
            state: KernelProofObject::root(ProofLocals::default(), {
                let context = BranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                };
                surface_goal
                    .map(|surface| {
                        OpenBranch::surface_proposition_in(context.clone(), goal.clone(), surface)
                    })
                    .unwrap_or_else(|| OpenBranch::proposition_in(context, goal))
            }),
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
                split_branches: Vec::new(),
            }),
        }
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(in crate::surface::proof) fn for_fixed_state_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        parameter_binding: ParameterBinding<'a>,
        pre_state: &'a ExecutionState,
        state: &'a ExecutionState,
        recorded_states: &'a RecordedStates,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            FixedStateFacts::Slice(available),
            |context| OpenBranch::proposition_in(context, goal),
            parameter_binding,
            FixedStateFrame::new(pre_state, state, None, recorded_states),
            None,
            surface_propositions,
            spec_definitions,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_fixed_state_surface_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        parameter_binding: ParameterBinding<'a>,
        pre_state: &'a ExecutionState,
        state: &'a ExecutionState,
        recorded_states: &'a RecordedStates,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            FixedStateFacts::Slice(available),
            |context| OpenBranch::surface_proposition_in(context, goal, surface_goal),
            parameter_binding,
            FixedStateFrame::new(pre_state, state, None, recorded_states),
            None,
            surface_propositions,
            spec_definitions,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(in crate::surface::proof) fn for_fixed_state_goal_with_requirements(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        parameter_binding: ParameterBinding<'a>,
        fixed_state: FixedStateFrame<'a>,
        premise_anchor: Option<&ProgramPointRef>,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
        original_requirements: &'a [Requirement],
    ) -> Self {
        Self::for_fixed_state_goal_with_requirements_inner(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::proposition_in(context, goal),
            parameter_binding,
            fixed_state,
            premise_anchor,
            surface_propositions,
            spec_definitions,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            original_requirements,
        )
    }

    #[cfg(test)]
    pub(super) fn for_fixed_state_goal_with_requirements_inner(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: impl FnOnce(BranchState) -> OpenBranch,
        parameter_binding: ParameterBinding<'a>,
        fixed_state: FixedStateFrame<'a>,
        premise_anchor: Option<&ProgramPointRef>,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
        original_requirements: &'a [Requirement],
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            FixedStateFacts::Slice(available),
            goal,
            parameter_binding,
            fixed_state,
            premise_anchor.cloned(),
            surface_propositions,
            spec_definitions,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            original_requirements,
            None,
        )
    }

    #[cfg(test)]
    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_fixed_state_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        parameter_binding: ParameterBinding<'a>,
        fixed_state: FixedStateFrame<'a>,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            FixedStateFacts::Slice(available),
            OpenBranch::frontier,
            parameter_binding,
            fixed_state,
            None,
            surface_propositions,
            spec_definitions,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    /// A frontier proof over a planning path's facts. The proof facts the
    /// list was copied from are extended by the facts it gained since,
    /// rather than every fact being indexed again.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn for_fixed_state_frontier_of_list(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a PureFactList,
        parameter_binding: ParameterBinding<'a>,
        fixed_state: FixedStateFrame<'a>,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            FixedStateFacts::List(available),
            OpenBranch::frontier,
            parameter_binding,
            fixed_state,
            None,
            surface_propositions,
            spec_definitions,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            Some(available.proof_facts()),
        )
    }

    pub(super) fn for_fixed_state(
        claim_label: &'a str,
        tactic_index: usize,
        available: FixedStateFacts<'a>,
        goal: impl FnOnce(BranchState) -> OpenBranch,
        parameter_binding: ParameterBinding<'a>,
        fixed_state: FixedStateFrame<'a>,
        premise_anchor: Option<ProgramPointRef>,
        surface_propositions: &'a SurfacePropositionMap,
        spec_definitions: SpecDefinitions<'a>,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &(impl ExecutionFactSource + ?Sized),
        original_requirements: &'a [Requirement],
        indexed: Option<ProofFacts>,
    ) -> Self {
        let facts = indexed.unwrap_or_else(|| ProofFacts::from_ordered(available.as_slice()));
        let lowering_context = resource_context_observable_facts_for_proof(
            fixed_state.state.resources(),
            facts.clone(),
        );
        let goal = goal(BranchState {
            facts,
            unfolded_predicates: PersistentOrderedSet::default(),
            execution: None,
        });
        let goal = match &goal.obligation {
            Obligation::Proposition(proposition) => goal.with_state(BranchState {
                facts: goal
                    .state
                    .facts
                    .with_selected_load_equality_bridge(proposition.kernel()),
                unfolded_predicates: goal.state.unfolded_predicates.clone(),
                execution: goal.state.execution.clone(),
            }),
            Obligation::Frontier(_) | Obligation::FunctionOutcome(_) => goal.clone(),
        };
        Self {
            site: ProofStepSite::default(),
            context: Arc::new(ProofContext::FixedState(FixedStateProofContext {
                claim_label,
                tactic_index,
                parameter_binding,
                fixed_state,
                premise_anchor,
                surface_propositions,
                spec_definitions,
                theorem_environment,
                unfolded_predicates,
                effect_facts: effect_facts.persistent_facts(),
                lowering_context,
                original_requirements,
                requirement_facts: available,
                nested_tactic_capture: None,
            })),
            state: KernelProofObject::root(ProofLocals::default(), goal),
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
                split_branches: Vec::new(),
            }),
        }
    }
}
