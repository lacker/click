//! Constructors for pure, fixed-state, and surface proof goals.

use super::*;

impl<'a> Proof<'a> {
    /// Reattributes subsequent execution-structure diagnostics to the source
    /// tactic that owns them without changing proof state or provenance.
    ///
    /// Simple steps carry their own origins. Structural operations span
    /// several checked transitions, so a long-lived function Proof updates
    /// this cursor metadata before entering each top-level structure.
    pub(in crate::lang::click::proof) fn with_execution_tactic_index(
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
            context: Arc::new(ProofContext::Execution(
                context.with_tactic_index(tactic_index),
            )),
            state: self.state.clone(),
            node: self.node.clone(),
            focused_branch: self.focused_branch,
        })
    }

    /// Restores an ancestor's exact execution diagnostic context after a
    /// nested structural operation. The descendant check is provenance-based;
    /// this changes no goals, facts, execution state, or proof nodes.
    pub(in crate::lang::click::proof) fn restore_execution_tactic_attribution(
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
            context: ancestor.context.clone(),
            state: self.state.clone(),
            node: self.node.clone(),
            focused_branch: self.focused_branch,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_pure_goal(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        theorem_context: &'a PureTheoremContext,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        Self::for_pure_goal_with_surface(
            claim_label,
            requires,
            goal,
            None,
            theorem_context,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_pure_surface_goal(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        theorem_context: &'a PureTheoremContext,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        Self::for_pure_goal_with_surface(
            claim_label,
            requires,
            goal,
            Some(surface_goal),
            theorem_context,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_pure_goal_with_surface(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
        theorem_context: &'a PureTheoremContext,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let facts = ProofFacts::from_ordered(requires);
        Self {
            context: Arc::new(ProofContext::Pure(PureProofContext {
                claim_label,
                theorem_context,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),

                open_branches: OpenBranches::root({
                    let context = BranchState {
                        facts,
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: None,
                    };
                    surface_goal
                        .map(|surface| {
                            OpenBranch::surface_proposition_in(
                                context.clone(),
                                goal.clone(),
                                surface,
                            )
                        })
                        .unwrap_or_else(|| OpenBranch::proposition_in(context, goal))
                }),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
            focused_branch: BranchId::ROOT,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_fixed_state_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::proposition_in(context, goal),
            parameters,
            arguments,
            pre_state,
            state,
            None,
            None,
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(in crate::lang::click::proof) fn for_fixed_state_surface_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::surface_proposition_in(context, goal, surface_goal),
            parameters,
            arguments,
            pre_state,
            state,
            None,
            None,
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    #[cfg(test)]
    pub(in crate::lang::click::proof) fn for_fixed_state_goal_with_requirements(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<&ProgramPointRef>,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: &'a BTreeMap<String, usize>,
    ) -> Self {
        Self::for_fixed_state_goal_with_requirements_inner(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::proposition_in(context, goal),
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor,
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            original_requirements,
            requirement_label_indices,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_fixed_state_surface_goal_with_requirements(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<&ProgramPointRef>,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: &'a BTreeMap<String, usize>,
    ) -> Self {
        Self::for_fixed_state_goal_with_requirements_inner(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::surface_proposition_in(context, goal, surface_goal),
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor,
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            original_requirements,
            requirement_label_indices,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_fixed_state_goal_with_requirements_inner(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: impl FnOnce(BranchState) -> OpenBranch,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<&ProgramPointRef>,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: &'a BTreeMap<String, usize>,
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            available,
            goal,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor.cloned(),
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            original_requirements,
            Some(requirement_label_indices),
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_fixed_state_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::frontier(EffectGoalSelection::None, context),
            parameters,
            arguments,
            pre_state,
            state,
            result,
            None,
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::lang::click::proof) fn for_fixed_state_frontier_with_premise_anchor(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<&ProgramPointRef>,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_fixed_state(
            claim_label,
            tactic_index,
            available,
            |context| OpenBranch::frontier(EffectGoalSelection::None, context),
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor.cloned(),
            recorded_snapshots,
            surface_propositions,
            predicate_environment,
            click_function_environment,
            theorem_environment,
            unfolded_predicates,
            effect_facts,
            &[],
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_fixed_state(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: impl FnOnce(BranchState) -> OpenBranch,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<ProgramPointRef>,
        recorded_snapshots: &'a RecordedSnapshots,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: Option<&'a BTreeMap<String, usize>>,
    ) -> Self {
        let facts = ProofFacts::from_ordered(available);
        let mut lowering_context = available.to_vec();
        append_resource_context_observable_facts(state.resources(), &mut lowering_context);
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
                    .with_selected_load_equality_bridge(&proposition.kernel),
                unfolded_predicates: goal.state.unfolded_predicates.clone(),
                execution: goal.state.execution.clone(),
            }),
            Obligation::Frontier(_) | Obligation::FunctionOutcome(_) => goal.clone(),
        };
        Self {
            context: Arc::new(ProofContext::FixedState(FixedStateProofContext {
                claim_label,
                tactic_index,
                parameters,
                arguments,
                pre_state,
                state,
                result,
                premise_anchor,
                recorded_snapshots,
                surface_propositions,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                unfolded_predicates,
                effect_facts,
                lowering_context: Arc::new(lowering_context),
                original_requirements,
                requirement_label_indices,
                requirement_facts: available,
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),

                open_branches: OpenBranches::root(goal),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
            focused_branch: BranchId::ROOT,
        }
    }
}
