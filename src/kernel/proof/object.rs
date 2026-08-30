//! Persistent checked proof-object state.
//!
//! Language-specific names and presentation records are opaque parameters.
//! The kernel owns the persistent state shape and never treats those
//! attachments as evidence.

use super::{
    BranchId, OutcomeProofState, ProofBranch, ProofBranchState, ProofBranches, ProofExecutionState,
    ProofFacts, ProofObligation,
};
use crate::kernel::Proposition;
use std::ops::Deref;
use std::sync::Arc;

/// The immutable state shared by checked proof successors.
#[derive(Clone)]
pub(crate) struct ProofState<L, O, E> {
    pub(crate) locals: L,
    pub(crate) open_branches: ProofBranches<ProofBranch<O, E>>,
    pub(crate) added_facts: Arc<Vec<Proposition>>,
    pub(crate) checked_facts: Arc<Vec<Proposition>>,
}

/// Opaque handle to one immutable checked proof state and the open branch it
/// addresses.
///
/// Surface-language context and certificate provenance deliberately live
/// outside this handle. They may describe or render a checked derivation, but
/// they are not part of the semantic proof state and cannot change its focus.
#[derive(Clone)]
pub(crate) struct ProofObject<L, O, E> {
    state: Arc<ProofState<L, O, E>>,
    focused_branch: BranchId,
}

/// Borrowed authority that the focused goal is an execution frontier owning
/// checked execution state. Only the kernel can construct this view.
pub(crate) struct ProofExecutionView<'a, S> {
    facts: &'a ProofFacts,
    execution: &'a ProofExecutionState<S>,
}

/// Kernel witness that no checked obligations remain open.
pub(crate) struct ProofCompletion<'a> {
    _proof: std::marker::PhantomData<&'a ()>,
}

#[derive(Clone, Copy)]
pub(crate) enum PropositionAssumptionContext {
    Exact,
    Pure,
    Materialized,
}

pub(crate) enum PropositionCloseError {
    NotProposition,
    Unavailable,
    DoesNotNormalize,
    ExpectedIntroduction(Proposition),
    ExpectedConjunction(Proposition),
    MissingConjuncts(Proposition, Proposition),
    ExpectedDisjunction(Proposition),
    MissingDisjunct(Proposition),
    ExpectedFiniteUniversal,
    MissingFiniteInstance,
    ContradictionUnavailable(Proposition),
}

#[derive(Clone, Copy)]
pub(crate) enum PropositionIntroduction {
    Implication,
    Universal { variable: crate::kernel::Variable },
    Negation,
}

impl<'a, S> ProofExecutionView<'a, S> {
    pub(crate) fn facts(&self) -> &'a ProofFacts {
        self.facts
    }

    pub(crate) fn execution(&self) -> &'a ProofExecutionState<S> {
        self.execution
    }
}

impl<L, O, E> ProofObject<L, O, E> {
    pub(crate) fn new(state: ProofState<L, O, E>, focused_branch: BranchId) -> Self {
        Self {
            state: Arc::new(state),
            focused_branch,
        }
    }

    pub(crate) fn from_shared_state(
        state: Arc<ProofState<L, O, E>>,
        focused_branch: BranchId,
    ) -> Self {
        Self {
            state,
            focused_branch,
        }
    }

    pub(crate) fn state(&self) -> &ProofState<L, O, E> {
        self.state.as_ref()
    }

    pub(crate) fn focused_branch(&self) -> BranchId {
        self.focused_branch
    }

    pub(crate) fn shares_state_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state, &other.state)
    }

    pub(crate) fn is_complete(&self) -> bool
    where
        O: Clone,
        E: Clone,
    {
        self.state.open_branches.is_empty()
    }

    pub(crate) fn completion(&self) -> Option<ProofCompletion<'_>>
    where
        O: Clone,
        E: Clone,
    {
        self.is_complete().then_some(ProofCompletion {
            _proof: std::marker::PhantomData,
        })
    }

    pub(crate) fn with_state(&self, state: ProofState<L, O, E>) -> Self {
        Self::new(state, self.focused_branch)
    }

    pub(crate) fn focused_at(&self, focused_branch: BranchId) -> Self {
        Self::from_shared_state(self.state.clone(), focused_branch)
    }

    pub(crate) fn into_state(self) -> ProofState<L, O, E>
    where
        L: Clone,
        O: Clone,
        E: Clone,
    {
        Arc::unwrap_or_clone(self.state)
    }
}

impl<L, P: Clone, O: Clone, S: Clone>
    ProofObject<L, ProofObligation<P, O>, ProofExecutionState<S>>
{
    pub(crate) fn execution_view(&self) -> Option<ProofExecutionView<'_, S>> {
        let branch = self.state.open_branches.get(self.focused_branch)?;
        if !matches!(branch.obligation, ProofObligation::Frontier(_)) {
            return None;
        }
        let execution = branch.state.execution.as_deref()?;
        Some(ProofExecutionView {
            facts: &branch.state.facts,
            execution,
        })
    }

    pub(crate) fn finalization(&self) -> Option<ProofExecutionView<'_, S>> {
        let view = self.execution_view()?;
        view.execution
            .core
            .frontier
            .is_at_function_exit()
            .then_some(view)
    }
}

impl<L: Clone, P: Clone, S: Clone, E: Clone>
    ProofObject<L, ProofObligation<P, Arc<OutcomeProofState<S>>>, E>
{
    fn focused_proposition(
        &self,
    ) -> Option<(
        &super::PropositionObligation<P, Arc<OutcomeProofState<S>>>,
        &ProofFacts,
    )> {
        let branch = self.state.open_branches.get(self.focused_branch)?;
        let ProofObligation::Proposition(goal) = &branch.obligation else {
            return None;
        };
        Some((goal, &branch.state.facts))
    }

    fn closed_focused(&self) -> Self {
        Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.close_at(self.focused_branch),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            self.focused_branch,
        )
    }

    pub(crate) fn apply_assumption(
        &self,
        context: PropositionAssumptionContext,
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let proposition = goal.proposition();
        let available = if let Some(outcome) = goal.outcome.as_deref() {
            facts.pure_assumption_available(proposition)
                || facts.available_across_effects(proposition, &outcome.core.effect_facts)
                || super::fact_reasoning::normalizes_context_free(proposition)
        } else {
            match context {
                PropositionAssumptionContext::Exact => facts.contains(proposition),
                PropositionAssumptionContext::Pure => {
                    facts.pure_assumption_available(proposition)
                        || super::fact_reasoning::normalizes_context_free(proposition)
                }
                PropositionAssumptionContext::Materialized => {
                    facts.materialization_available(proposition)
                        || facts.contains_discharged_implication_consequent(proposition)
                        || super::fact_reasoning::normalizes_context_free(proposition)
                }
            }
        };
        available
            .then(|| self.closed_focused())
            .ok_or(PropositionCloseError::Unavailable)
    }

    pub(crate) fn apply_normalize(&self) -> Result<Self, PropositionCloseError> {
        let (goal, _) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        super::fact_reasoning::normalizes_context_free(goal.proposition())
            .then(|| self.closed_focused())
            .ok_or(PropositionCloseError::DoesNotNormalize)
    }

    pub(crate) fn apply_intro(
        &self,
        presentation: impl FnOnce(&P, PropositionIntroduction) -> P,
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let (proposition, introduced, introduction) = match goal.proposition() {
            Proposition::Implies(antecedent, consequent) => (
                consequent.as_ref().clone(),
                Some(antecedent.as_ref().clone()),
                PropositionIntroduction::Implication,
            ),
            Proposition::ForAll { var, body, .. } => (
                body.as_ref().clone(),
                None,
                PropositionIntroduction::Universal { variable: *var },
            ),
            Proposition::Not(body) => (
                Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true),
                Some(body.as_ref().clone()),
                PropositionIntroduction::Negation,
            ),
            other => {
                return Err(PropositionCloseError::ExpectedIntroduction(other.clone()));
            }
        };
        let presentation = presentation(&goal.presentation, introduction);
        let obligation = match goal.outcome.clone() {
            Some(outcome) => {
                super::PropositionObligation::at_outcome(proposition, presentation, outcome)
            }
            None => super::PropositionObligation::new(proposition, presentation),
        };
        let added_facts = introduced.into_iter().collect::<Vec<_>>();
        let mut facts = facts.clone();
        for fact in &added_facts {
            facts = facts.with_fact(fact.clone());
        }
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .expect("a proposition introduction retains its focused branch");
        let branch_state = ProofBranchState {
            facts,
            unfolded_predicates: branch.state.unfolded_predicates.clone(),
            execution: branch.state.execution.clone(),
        };
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.replace_at(
                    self.focused_branch,
                    ProofBranch::new(ProofObligation::Proposition(obligation), branch_state),
                ),
                checked_facts: Arc::new(added_facts.clone()),
                added_facts: Arc::new(added_facts),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn apply_split(&self) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let Proposition::And(left, right) = goal.proposition() else {
            return Err(PropositionCloseError::ExpectedConjunction(
                goal.proposition().clone(),
            ));
        };
        if !facts.contains(left) || !facts.contains(right) {
            return Err(PropositionCloseError::MissingConjuncts(
                left.as_ref().clone(),
                right.as_ref().clone(),
            ));
        }
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_disjunct(&self, take_left: bool) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let Proposition::Or(left, right) = goal.proposition() else {
            return Err(PropositionCloseError::ExpectedDisjunction(
                goal.proposition().clone(),
            ));
        };
        let selected = if take_left {
            left.as_ref()
        } else {
            right.as_ref()
        };
        if !facts.contains(selected)
            && !super::fact_reasoning::condition_polarity_forms(selected)
                .iter()
                .any(|form| facts.contains(form))
        {
            return Err(PropositionCloseError::MissingDisjunct(selected.clone()));
        }
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_enumerate(&self) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal.proposition())
        else {
            return Err(PropositionCloseError::ExpectedFiniteUniversal);
        };
        for (_, instance) in instances {
            if !super::fact_reasoning::normalizes_context_free(&instance)
                && !facts.contains(&instance)
            {
                return Err(PropositionCloseError::MissingFiniteInstance);
            }
        }
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_contradiction(
        &self,
        fact: &Proposition,
    ) -> Result<Self, PropositionCloseError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionCloseError::Unavailable)?;
        let negated = Proposition::Not(Box::new(fact.clone()));
        let opposite_condition = match fact {
            Proposition::ConditionIs(condition, value) => {
                Some(Proposition::ConditionIs(condition.clone(), !value))
            }
            _ => None,
        };
        let contradictory = branch.state.facts.contains(fact)
            && (branch.state.facts.contains(&negated)
                || opposite_condition
                    .as_ref()
                    .is_some_and(|opposite| branch.state.facts.contains(opposite))
                || super::fact_reasoning::normalizes_context_free(&negated));
        contradictory
            .then(|| self.closed_focused())
            .ok_or_else(|| PropositionCloseError::ContradictionUnavailable(fact.clone()))
    }
}

impl<L, O, E> Deref for ProofObject<L, O, E> {
    type Target = ProofState<L, O, E>;

    fn deref(&self) -> &Self::Target {
        self.state()
    }
}

impl<P: Clone, O: Clone, E: Clone> ProofBranches<ProofBranch<ProofObligation<P, O>, E>> {
    pub(crate) fn obligation(&self, at: BranchId) -> Option<&ProofObligation<P, O>> {
        Some(&self.get(at)?.obligation)
    }

    /// Replaces only what the addressed branch must establish, preserving its
    /// branch-local state.
    pub(crate) fn replace_obligation_at(
        &self,
        at: BranchId,
        obligation: ProofObligation<P, O>,
    ) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("obligation refinement requires the addressed open branch");
        };
        self.replace_at(at, branch.with_obligation(obligation))
    }

    /// Retains the addressed obligation under updated branch-local state.
    pub(crate) fn with_branch_state_at(&self, at: BranchId, state: ProofBranchState<E>) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("a state successor requires the addressed open branch");
        };
        self.replace_at(at, branch.with_state(state))
    }

    /// Retains the addressed goal under updated facts, preserving any
    /// execution snapshot it already borrowed.
    pub(crate) fn with_facts_at(&self, at: BranchId, facts: ProofFacts) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("a fact successor requires the addressed open branch");
        };
        self.with_branch_state_at(
            at,
            ProofBranchState {
                facts,
                unfolded_predicates: branch.state.unfolded_predicates.clone(),
                execution: branch.state.execution.clone(),
            },
        )
    }

    /// Retains the addressed goal under an updated execution snapshot and
    /// facts. The successor preserves the goal's kind.
    pub(crate) fn replace_execution_at(
        &self,
        at: BranchId,
        facts: ProofFacts,
        execution: E,
    ) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("an execution successor requires the addressed open branch");
        };
        self.with_branch_state_at(
            at,
            ProofBranchState {
                facts,
                unfolded_predicates: branch.state.unfolded_predicates.clone(),
                execution: Some(Arc::new(execution)),
            },
        )
    }

    /// The strict frontier successor: the addressed obligation must be an
    /// execution frontier.
    pub(crate) fn replace_frontier_at(
        &self,
        at: BranchId,
        facts: ProofFacts,
        execution: E,
    ) -> Self {
        let Some(ProofBranch {
            obligation: ProofObligation::Frontier(_),
            ..
        }) = self.get(at)
        else {
            unreachable!("a frontier transition requires the addressed frontier goal");
        };
        self.replace_execution_at(at, facts, execution)
    }

    pub(crate) fn discharged_if_at(&self, at: BranchId, complete: bool, facts: ProofFacts) -> Self {
        if complete {
            self.close_at(at)
        } else {
            self.with_facts_at(at, facts)
        }
    }

    pub(crate) fn discharged_if_or_execution_at(
        &self,
        at: BranchId,
        complete: bool,
        facts: ProofFacts,
        execution: E,
    ) -> Self {
        if complete {
            self.close_at(at)
        } else {
            self.replace_execution_at(at, facts, execution)
        }
    }

    pub(crate) fn is_discharged(&self) -> bool {
        self.is_empty()
    }
}
