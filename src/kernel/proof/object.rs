//! Persistent checked proof-object state.
//!
//! Language-specific names and presentation records are opaque parameters.
//! The kernel owns the persistent state shape and never treats those
//! attachments as evidence.

use super::{
    BranchId, CheckedProofCasePartition, FrontierObligation, OutcomeProofState,
    PersistentOrderedSet, ProofBranch, ProofBranchState, ProofBranches, ProofExecutionState,
    ProofFacts, ProofObligation,
};
use crate::kernel::{Proposition, Sort};
use std::ops::Deref;
use std::sync::Arc;

/// The immutable state shared by checked proof successors. Its fields stay
/// private so code outside this module can inspect the state but cannot
/// assemble a whole semantic successor.
#[derive(Clone)]
pub(crate) struct ProofState<L, O, E> {
    locals: L,
    open_branches: ProofBranches<ProofBranch<O, E>>,
    added_facts: Arc<Vec<Proposition>>,
    checked_facts: Arc<Vec<Proposition>>,
}

impl<L, O, E> ProofState<L, O, E> {
    pub(crate) fn locals(&self) -> &L {
        &self.locals
    }

    pub(crate) fn open_branches(&self) -> &ProofBranches<ProofBranch<O, E>> {
        &self.open_branches
    }

    pub(crate) fn added_facts(&self) -> &[Proposition] {
        &self.added_facts
    }

    pub(crate) fn checked_facts(&self) -> &[Proposition] {
        &self.checked_facts
    }

    #[cfg(test)]
    pub(crate) fn open_branches_mut(&mut self) -> &mut ProofBranches<ProofBranch<O, E>> {
        &mut self.open_branches
    }
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

/// A kernel-created exact invariant judgment, paired with its execution inputs.
/// Callers can run the root but cannot replace the judgment or its premises.
#[cfg_attr(test, derive(Clone))]
pub(crate) struct InvariantBodyScope<L, O, E> {
    root: ProofObject<L, O, E>,
    binding: super::execution::CheckedLoopInvariantLowerings,
}

#[derive(Clone)]
pub(super) struct CheckedInvariantBody {
    goal: Proposition,
    proof: super::CheckedProposition,
}

impl CheckedInvariantBody {
    pub(super) fn recheck(&self) -> bool {
        self.proof.proposition() == &self.goal
    }
}

pub(crate) struct ProofSplit<L, O, E> {
    proof: ProofObject<L, O, E>,
    split: super::SplitId,
    branches: [BranchId; 2],
    introduced_facts: [Vec<Proposition>; 2],
}

pub(crate) enum PropositionSplitError {
    Completed,
    NotProposition,
    MissingDisjunction(Proposition),
    ExpectedDisjunction(Proposition),
    NonComplementaryCases,
}

pub(crate) enum ProofJoinError {
    InvalidSplit,
    ArmIncomplete(usize),
}

pub(crate) enum ProofFocusError {
    NotOpen,
}

pub(crate) enum FrontierSplitError {
    Completed,
    NotFrontier,
    MissingExecution,
    #[cfg(test)]
    MissingDisjunction(Proposition),
    #[cfg(test)]
    ExpectedDisjunction(Proposition),
    NonComplementaryCases,
}

pub(crate) enum ExecutionUpdateError {
    NotFrontier,
    MissingExecution,
    NotLoopBody,
    InvariantsAlreadyClosed,
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
    ConditionalNormalization(super::fact_reasoning::ConditionalNormalizationError),
    ArithmeticPremiseUnavailable(usize),
    Arithmetic(super::fact_reasoning::ArithmeticCheckError),
    IntegerArithmeticPremiseUnavailable(usize),
    IntegerArithmetic(super::integer_arithmetic::IntegerArithmeticCheckError),
    ExpectedIntroduction(Proposition),
    ExpectedConjunction(Proposition),
    MissingConjuncts(Proposition, Proposition),
    ExpectedDisjunction(Proposition),
    MissingDisjunct(Proposition),
    ExpectedFiniteUniversal,
    MissingFiniteInstance,
    ContradictionUnavailable(Proposition),
    ExtractUnavailable(Proposition),
    InstantiatePremiseUnavailable(Proposition),
    InstantiateQuantifiedUnavailable,
    InstantiateInvalid(super::fact_reasoning::ForallInt32InstantiationError),
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
    pub(crate) fn root(locals: L, branch: ProofBranch<O, E>) -> Self
    where
        O: Clone,
        E: Clone,
    {
        Self::new(
            ProofState {
                locals,
                open_branches: ProofBranches::root(branch),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            BranchId::ROOT,
        )
    }

    fn new(state: ProofState<L, O, E>, focused_branch: BranchId) -> Self {
        Self {
            state: Arc::new(state),
            focused_branch,
        }
    }

    fn from_shared_state(state: Arc<ProofState<L, O, E>>, focused_branch: BranchId) -> Self {
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

    #[cfg(test)]
    pub(crate) fn with_state(&self, state: ProofState<L, O, E>) -> Self {
        Self::new(state, self.focused_branch)
    }

    #[cfg(test)]
    pub(crate) fn into_state(self) -> ProofState<L, O, E>
    where
        L: Clone,
        O: Clone,
        E: Clone,
    {
        Arc::unwrap_or_clone(self.state)
    }
}

impl<L: Clone, O: Clone, E: Clone> ProofObject<L, O, E> {
    pub(crate) fn focus_open_branch(
        &self,
        focused_branch: BranchId,
    ) -> Result<Self, ProofFocusError> {
        if self.state.open_branches.get(focused_branch).is_none() {
            return Err(ProofFocusError::NotOpen);
        }
        Ok(Self::from_shared_state(self.state.clone(), focused_branch))
    }

    pub(crate) fn focus_open_branch_with_fact_deltas(
        &self,
        focused_branch: BranchId,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ProofFocusError> {
        Ok(self
            .focus_open_branch(focused_branch)?
            .with_fact_deltas(added_facts, checked_facts))
    }

    pub(crate) fn with_fact_deltas(
        &self,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Self {
        Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.clone(),
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            },
            self.focused_branch,
        )
    }

    /// Replace the language's lexical environment without changing any
    /// semantic goal, premise, branch, or evidence.
    pub(crate) fn with_locals(&self, locals: L) -> Self {
        Self::new(
            ProofState {
                locals,
                open_branches: self.state.open_branches.clone(),
                added_facts: self.state.added_facts.clone(),
                checked_facts: self.state.checked_facts.clone(),
            },
            self.focused_branch,
        )
    }
}

impl<L: Clone, O: Clone, E: Clone> ProofObject<L, O, E> {
    pub(in crate::kernel) fn publish_checked_focused_result(
        &self,
        locals: L,
        branch: Option<ProofBranch<O, E>>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ProofFocusError> {
        if self.state.open_branches.get(self.focused_branch).is_none() {
            return Err(ProofFocusError::NotOpen);
        }
        let open_branches = match branch {
            Some(branch) => self
                .state
                .open_branches
                .replace_at(self.focused_branch, branch),
            None => self.state.open_branches.close_at(self.focused_branch),
        };
        Ok(Self::new(
            ProofState {
                locals,
                open_branches,
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            },
            self.focused_branch,
        ))
    }

    /// Publishes a focused result assembled by the checked kernel proof
    /// drivers. The raw state replacement stays kernel-scoped; this adapter
    /// is the one route used by the language layer after its operation-specific
    /// checker has produced the result and fact deltas.
    pub(crate) fn publish_checked_result(
        &self,
        locals: L,
        branch: Option<ProofBranch<O, E>>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ProofFocusError> {
        self.publish_checked_focused_result(locals, branch, added_facts, checked_facts)
    }

    pub(crate) fn replace_focused_with_checked_branches(
        &self,
        branches: Vec<ProofBranch<O, E>>,
    ) -> Result<(Self, Vec<BranchId>), ProofFocusError> {
        if self.state.open_branches.get(self.focused_branch).is_none() || branches.is_empty() {
            return Err(ProofFocusError::NotOpen);
        }
        let mut open_branches = self.state.open_branches.close_at(self.focused_branch);
        let mut ids = Vec::with_capacity(branches.len());
        for branch in branches {
            let (id, next) = open_branches.push(branch);
            ids.push(id);
            open_branches = next;
        }
        Ok((
            Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                ids[0],
            ),
            ids,
        ))
    }

    pub(crate) fn replace_focused_obligation(
        &self,
        obligation: O,
    ) -> Result<Self, ProofFocusError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ProofFocusError::NotOpen)?;
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .replace_at(self.focused_branch, branch.with_obligation(obligation)),
                added_facts: self.state.added_facts.clone(),
                checked_facts: self.state.checked_facts.clone(),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn replace_focused_obligation_and_facts(
        &self,
        obligation: O,
        facts: ProofFacts,
    ) -> Result<Self, ProofFocusError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ProofFocusError::NotOpen)?;
        let state = ProofBranchState {
            facts,
            unfolded_predicates: branch.state.unfolded_predicates.clone(),
            execution: branch.state.execution.clone(),
        };
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .replace_at(self.focused_branch, ProofBranch::new(obligation, state)),
                added_facts: self.state.added_facts.clone(),
                checked_facts: self.state.checked_facts.clone(),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn publish_checked_focused_transition(
        &self,
        obligation: O,
        facts: ProofFacts,
        execution: Option<Arc<E>>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ProofFocusError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ProofFocusError::NotOpen)?;
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.replace_at(
                    self.focused_branch,
                    ProofBranch::new(
                        obligation,
                        ProofBranchState {
                            facts,
                            unfolded_predicates: branch.state.unfolded_predicates.clone(),
                            execution,
                        },
                    ),
                ),
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn join_closed_split(
        &self,
        split: super::SplitId,
        branches: [BranchId; 2],
        parent: BranchId,
    ) -> Result<Self, ProofJoinError> {
        if !split.owns(branches) || !split.follows(parent) {
            return Err(ProofJoinError::InvalidSplit);
        }
        for (arm, branch) in branches.into_iter().enumerate() {
            if self.state.open_branches.get(branch).is_some() {
                return Err(ProofJoinError::ArmIncomplete(arm));
            }
        }
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.clone(),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            parent,
        ))
    }
}

impl<L, O, E> ProofSplit<L, O, E> {
    pub(crate) fn into_parts(self) -> (ProofObject<L, O, E>, super::SplitId, [BranchId; 2]) {
        (self.proof, self.split, self.branches)
    }

    pub(crate) fn into_parts_with_facts(
        self,
    ) -> (
        ProofObject<L, O, E>,
        super::SplitId,
        [BranchId; 2],
        [Vec<Proposition>; 2],
    ) {
        (self.proof, self.split, self.branches, self.introduced_facts)
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
    /// Returns an owned, kernel-issued record of the exact root proposition
    /// discharged by this proof. The record is available only after every
    /// branch in the proof lineage has closed.
    pub(crate) fn completed_proposition(&self) -> Option<super::CheckedProposition> {
        self.completion()?;
        let ProofObligation::Proposition(goal) = &self.state.open_branches.root_branch().obligation
        else {
            return None;
        };
        Some(super::CheckedProposition::new(
            goal.proposition().clone(),
            goal.outcome.as_deref().map(|outcome| outcome.core.clone()),
            self.state
                .open_branches
                .root_branch()
                .state
                .facts
                .is_empty(),
        ))
    }

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
        } else {
            match context {
                PropositionAssumptionContext::Exact => facts.contains(proposition),
                PropositionAssumptionContext::Pure => facts.pure_assumption_available(proposition),
                PropositionAssumptionContext::Materialized => {
                    facts.materialization_available(proposition)
                }
            }
        };
        available
            .then(|| self.closed_focused())
            .ok_or(PropositionCloseError::Unavailable)
    }

    /// An interface leaf uses indexed premises, direct intrinsic facts, or
    /// an exact kernel-issued load definition; it never selects a derivation.
    pub(super) fn apply_interface_leaf(
        &self,
        definition: Option<&super::execution::CheckedInterfaceLoadDefinition>,
        read_premise: Option<&Proposition>,
    ) -> Option<Self> {
        let (goal, facts) = self.focused_proposition()?;
        (super::execution::checked_branch_fact_is_available(facts, goal.proposition())
            || definition.is_some_and(|definition| definition.proves(goal.proposition()))
            || read_premise.is_some_and(|premise| {
                facts.contains(premise)
                    && super::execution::interface_read_is_subrange(goal.proposition(), premise)
            }))
        .then(|| self.closed_focused())
    }

    pub(super) fn apply_resource_delta(&self) -> Option<Self> {
        let (goal, _) = self.focused_proposition()?;
        let Proposition::Implies(source, conclusion) = goal.proposition() else {
            return None;
        };
        (super::execution::resource_read_preserves_range(source, conclusion)
            || matches!(conclusion.as_ref(), Proposition::Implies(equality, goal)
                if super::execution::resource_delta_uses_exact_equality(source, equality, goal)))
        .then(|| self.closed_focused())
    }

    pub(crate) fn apply_normalize(&self) -> Result<Self, PropositionCloseError> {
        let (goal, _) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        super::fact_reasoning::normalizes_context_free_leaf(goal.proposition())
            .then(|| self.closed_focused())
            .ok_or(PropositionCloseError::DoesNotNormalize)
    }

    pub(crate) fn apply_normalize_using(
        &self,
        premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        super::fact_reasoning::normalize_using_conditions(goal.proposition(), premises, facts)
            .map_err(PropositionCloseError::ConditionalNormalization)?;
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_arithmetic(
        &self,
        premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        for (index, premise) in premises.iter().enumerate() {
            if !facts.exact_available_across_effects(premise, &[]) {
                return Err(PropositionCloseError::ArithmeticPremiseUnavailable(index));
            }
        }
        if super::fact_reasoning::check_float_reflexive_comparison(goal.proposition(), premises)
            || super::fact_reasoning::check_pointer_alignment_arithmetic(
                goal.proposition(),
                premises,
            )
        {
            return Ok(self.closed_focused());
        }
        super::fact_reasoning::check_signed_affine_arithmetic(goal.proposition(), premises)
            .map_err(PropositionCloseError::Arithmetic)?;
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_integer_arithmetic(
        &self,
        certificate: &super::integer_arithmetic::IntegerArithmeticCertificate,
        premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        for (index, premise) in premises.iter().enumerate() {
            if !facts.exact_available_across_effects(premise, &[]) {
                return Err(PropositionCloseError::IntegerArithmeticPremiseUnavailable(
                    index,
                ));
            }
        }
        certificate
            .check(goal.proposition(), premises)
            .map_err(PropositionCloseError::IntegerArithmetic)?;
        Ok(self.closed_focused())
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
            Proposition::ForAll { var, sort, body } => {
                let (variable, body) = match sort {
                    Sort::CPointer(c_type) => {
                        facts.freshen_pointer_forall_body(*var, *c_type, body)
                    }
                    _ => facts.freshen_int32_forall_body(*var, body),
                };
                (body, None, PropositionIntroduction::Universal { variable })
            }
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
            if super::fact_reasoning::normalizes_context_free(&instance)
                || facts.contains(&instance)
            {
                continue;
            }
            // An instance whose guard is constant true is held as its
            // conclusion, the form a proof states it in.
            if let Proposition::Implies(guard, conclusion) = &instance
                && super::fact_reasoning::normalizes_context_free(guard)
                && facts.contains(conclusion)
            {
                continue;
            }
            return Err(PropositionCloseError::MissingFiniteInstance);
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
        branch
            .state
            .facts
            .contradicts(fact)
            .then(|| self.closed_focused())
            .ok_or_else(|| PropositionCloseError::ContradictionUnavailable(fact.clone()))
    }

    pub(crate) fn apply_extract(
        &self,
        proposition: Proposition,
    ) -> Result<Self, PropositionCloseError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionCloseError::Unavailable)?;
        if !branch.state.facts.contains_proper_conjunct(&proposition)
            && !branch
                .state
                .facts
                .contains_discharged_implication_consequent(&proposition)
            && !branch
                .state
                .facts
                .assumptions()
                .contains_algebraic_constructor_field_equality(&proposition)
        {
            return Err(PropositionCloseError::ExtractUnavailable(proposition));
        }
        let added_facts = (!branch.state.facts.contains_top_level(&proposition))
            .then(|| proposition.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = branch.state.facts.with_fact(proposition);
        let complete = match &branch.obligation {
            ProofObligation::Proposition(goal) => facts.contains(goal.proposition()),
            _ => false,
        };
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.discharged_if_at(
                    self.focused_branch,
                    complete,
                    facts,
                ),
                checked_facts: Arc::new(added_facts.clone()),
                added_facts: Arc::new(added_facts),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn apply_instantiate(
        &self,
        quantified: Proposition,
        argument: crate::kernel::Bitvector32Term,
        explicit_premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (_, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        for premise in explicit_premises {
            if !facts.available_across_effects(premise, &[]) {
                return Err(PropositionCloseError::InstantiatePremiseUnavailable(
                    premise.clone(),
                ));
            }
        }
        let quantified = if facts.contains(&quantified) {
            quantified
        } else if let Some(available) = facts.matching_quantified_fact(&quantified) {
            available
        } else {
            return Err(PropositionCloseError::InstantiateQuantifiedUnavailable);
        };
        let conclusion = super::fact_reasoning::check_forall_int32_instantiation(
            &quantified,
            argument,
            explicit_premises,
        )
        .map_err(PropositionCloseError::InstantiateInvalid)?;
        let added_facts = (!facts.contains_top_level(&conclusion))
            .then(|| conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = facts.with_fact(conclusion);
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .with_facts_at(self.focused_branch, facts),
                checked_facts: Arc::new(added_facts.clone()),
                added_facts: Arc::new(added_facts),
            },
            self.focused_branch,
        ))
    }

    /// Open the exact conjuncts without introducing either as an assumption.
    pub(crate) fn split_proposition_both(
        &self,
        presentation: impl Fn(&P, bool) -> P,
    ) -> Result<ProofSplit<L, ProofObligation<P, Arc<OutcomeProofState<S>>>, E>, &'static str> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or("`both` follows a completed proof")?;
        let ProofObligation::Proposition(goal) = &branch.obligation else {
            return Err("`both` requires a proposition goal");
        };
        let Proposition::And(left, right) = goal.proposition() else {
            return Err("`both` requires an `and` goal");
        };
        let arm = |proposition: &Proposition, left: bool| {
            let mut child = super::PropositionObligation::new(
                proposition.clone(),
                presentation(&goal.presentation, left),
            );
            child.outcome = goal.outcome.clone();
            ProofBranch::new(ProofObligation::Proposition(child), branch.state.clone())
        };
        let (split, branches, open_branches) = self
            .state
            .open_branches
            .split_at(self.focused_branch, [arm(left, true), arm(right, false)]);
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts: [Vec::new(), Vec::new()],
        })
    }

    pub(crate) fn split_proposition_cases(
        &self,
        disjunction: Proposition,
    ) -> Result<
        ProofSplit<L, ProofObligation<P, Arc<OutcomeProofState<S>>>, E>,
        PropositionSplitError,
    > {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionSplitError::Completed)?;
        let ProofObligation::Proposition(goal) = &branch.obligation else {
            return Err(PropositionSplitError::NotProposition);
        };
        if !branch.state.facts.contains(&disjunction) {
            return Err(PropositionSplitError::MissingDisjunction(disjunction));
        }
        let Proposition::Or(left, right) = disjunction else {
            return Err(PropositionSplitError::ExpectedDisjunction(disjunction));
        };
        let arm = |disjunct: Proposition| {
            ProofBranch::new(
                ProofObligation::Proposition(goal.clone()),
                ProofBranchState {
                    facts: branch.state.facts.with_fact(disjunct),
                    unfolded_predicates: branch.state.unfolded_predicates.clone(),
                    execution: branch.state.execution.clone(),
                },
            )
        };
        let (split, branches, open_branches) = self
            .state
            .open_branches
            .split_at(self.focused_branch, [arm(*left), arm(*right)]);
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts: [Vec::new(), Vec::new()],
        })
    }

    pub(crate) fn split_proposition_if(
        &self,
        then_fact: Proposition,
        else_fact: Proposition,
    ) -> Result<
        ProofSplit<L, ProofObligation<P, Arc<OutcomeProofState<S>>>, E>,
        PropositionSplitError,
    > {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionSplitError::Completed)?;
        let ProofObligation::Proposition(goal) = &branch.obligation else {
            return Err(PropositionSplitError::NotProposition);
        };
        let negated_then = Proposition::Not(Box::new(then_fact.clone()));
        if else_fact != negated_then
            && !super::fact_reasoning::condition_polarity_forms(&negated_then).contains(&else_fact)
        {
            return Err(PropositionSplitError::NonComplementaryCases);
        }
        let arm = |fact: Proposition| {
            ProofBranch::new(
                ProofObligation::Proposition(goal.clone()),
                ProofBranchState {
                    facts: branch.state.facts.with_fact(fact),
                    unfolded_predicates: branch.state.unfolded_predicates.clone(),
                    execution: branch.state.execution.clone(),
                },
            )
        };
        let (split, branches, open_branches) = self
            .state
            .open_branches
            .split_at(self.focused_branch, [arm(then_fact), arm(else_fact)]);
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts: [Vec::new(), Vec::new()],
        })
    }
}

impl<L: Clone, P: Clone, T: Clone, S: Clone>
    ProofObject<L, ProofObligation<P, Arc<OutcomeProofState<T>>>, ProofExecutionState<S>>
{
    /// The kernel constructs the exact root and its complete premises. The
    /// language supplies presentation only, never obligations or assumptions.
    pub(crate) fn open_invariant_body(
        &self,
        loop_entry: &crate::kernel::CState,
        checks: &[crate::kernel::CLoopInvariantCheck],
        presentation: impl FnOnce(&Proposition) -> P,
    ) -> Result<
        (
            Self,
            InvariantBodyScope<
                L,
                ProofObligation<P, Arc<OutcomeProofState<T>>>,
                ProofExecutionState<S>,
            >,
        ),
        String,
    > {
        let (branch, execution) = self
            .focused_frontier_execution()
            .map_err(|_| "invariant body requires an execution frontier")?;
        if execution.core.frontier.region != super::ExecutionRegionKind::LoopBody
            || !execution.core.frontier.is_at_region_boundary()
            || execution.core.region_invariants_close_requested
        {
            return Err("invariant body requires an unclosed loop back edge".into());
        }
        let mut facts = branch.state.facts.clone();
        for fact in execution.core.effect_facts.iter() {
            facts = facts.with_fact(fact.proposition().clone());
        }
        for fact in crate::kernel::certified_store_equations(&execution.core.effect_facts) {
            facts = facts.with_fact(fact);
        }
        let obligations = crate::kernel::c_loop_invariant_obligations_at_back_edge(
            &execution.core.state,
            loop_entry,
            checks,
            facts.assumptions(),
        )
        .map_err(|_| "could not lower explicit invariant obligations")?;
        let goal = obligations
            .iter()
            .rev()
            .map(|obligation| obligation.proposition().clone())
            .reduce(|right, left| Proposition::And(Box::new(left), Box::new(right)))
            .unwrap_or(Proposition::ConditionIs(
                crate::kernel::ConditionTerm::Constant(true),
                true,
            ));
        let display = presentation(&goal);
        let root = Self::root(
            self.state.locals.clone(),
            ProofBranch::new(
                ProofObligation::Proposition(super::PropositionObligation::new(goal, display)),
                ProofBranchState {
                    facts,
                    unfolded_predicates: branch.state.unfolded_predicates.clone(),
                    execution: branch.state.execution.clone(),
                },
            ),
        );
        let scope = InvariantBodyScope {
            root: root.clone(),
            binding: super::execution::CheckedLoopInvariantLowerings {
                snapshot: execution.core.state.clone(),
                checks: checks.to_vec(),
                facts: branch.state.facts.clone(),
                effects: execution.core.effect_facts.clone(),
                body: None,
            },
        };
        Ok((root, scope))
    }

    /// Retain the completed proof's own checked result, never a result minted
    /// from the requested goal. Exact root identity additionally binds its
    /// assumptions and all conjuncts to the kernel-created scope.
    pub(crate) fn retain_invariant_body(
        &self,
        scope: InvariantBodyScope<
            L,
            ProofObligation<P, Arc<OutcomeProofState<T>>>,
            ProofExecutionState<S>,
        >,
        completed: &Self,
    ) -> Result<Self, String> {
        if !std::ptr::eq(
            scope.root.state.open_branches.root_branch(),
            completed.state.open_branches.root_branch(),
        ) {
            return Err("invariant body belongs to another proof root".into());
        }
        let proof = completed
            .completed_proposition()
            .ok_or("invariant body has incomplete obligations")?;
        let ProofObligation::Proposition(goal) =
            &scope.root.state.open_branches.root_branch().obligation
        else {
            return Err("invariant body lost its proposition root".into());
        };
        if proof.proposition() != goal.proposition() {
            return Err("invariant body completed a different judgment".into());
        }
        let (branch, execution) = self
            .focused_frontier_execution()
            .map_err(|_| "invariant body requires an execution frontier")?;
        if !execution.core.frontier.is_at_region_boundary() {
            return Err("invariant body requires the loop back edge".into());
        }
        if !scope
            .binding
            .snapshot
            .shares_storage_with(&execution.core.state)
            || !scope
                .binding
                .facts
                .shares_premises_with(&branch.state.facts)
            || !scope
                .binding
                .effects
                .shares_storage_with(&execution.core.effect_facts)
        {
            return Err("invariant body belongs to another execution context".into());
        }
        let mut binding = scope.binding;
        binding.body = Some(CheckedInvariantBody {
            goal: goal.proposition().clone(),
            proof,
        });
        let requested = self
            .request_frontier_invariant_closure()
            .map_err(|_| "invariant body requires an unclosed loop frontier")?;
        let (branch, execution) = requested
            .focused_frontier_execution()
            .map_err(|_| "invariant body lost its frontier")?;
        let mut core = execution.core.clone();
        core.checked_invariant_lowerings = Some(Arc::new(binding));
        Ok(Self::new(
            ProofState {
                locals: requested.state.locals.clone(),
                open_branches: requested.state.open_branches.with_branch_state_at(
                    requested.focused_branch,
                    ProofBranchState {
                        facts: branch.state.facts.clone(),
                        unfolded_predicates: branch.state.unfolded_predicates.clone(),
                        execution: Some(Arc::new(ProofExecutionState::new(
                            core,
                            execution.presentation.clone(),
                        ))),
                    },
                ),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            requested.focused_branch,
        ))
    }
}

impl<L: Clone, P: Clone, O: Clone, S: Clone>
    ProofObject<L, ProofObligation<P, O>, ProofExecutionState<S>>
{
    fn focused_frontier_execution(
        &self,
    ) -> Result<
        (
            &ProofBranch<ProofObligation<P, O>, ProofExecutionState<S>>,
            &ProofExecutionState<S>,
        ),
        ExecutionUpdateError,
    > {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ExecutionUpdateError::NotFrontier)?;
        if !matches!(branch.obligation, ProofObligation::Frontier(_)) {
            return Err(ExecutionUpdateError::NotFrontier);
        }
        let execution = branch
            .state
            .execution
            .as_deref()
            .ok_or(ExecutionUpdateError::MissingExecution)?;
        Ok((branch, execution))
    }

    pub(crate) fn replace_frontier_presentation(
        &self,
        presentation: S,
    ) -> Result<Self, ExecutionUpdateError> {
        let (branch, execution) = self.focused_frontier_execution()?;
        let state = ProofBranchState {
            facts: branch.state.facts.clone(),
            unfolded_predicates: branch.state.unfolded_predicates.clone(),
            execution: Some(Arc::new(ProofExecutionState::new(
                execution.core.clone(),
                presentation,
            ))),
        };
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .with_branch_state_at(self.focused_branch, state),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            self.focused_branch,
        ))
    }

    /// Applies a language-only metadata edit without exposing or replacing
    /// the checked execution core, branch facts, obligation, or proof deltas.
    ///
    /// Consuming the handle preserves the existing copy-on-write behavior:
    /// uniquely owned state and presentation roots are edited without an
    /// otherwise unnecessary clone.
    pub(crate) fn edit_frontier_presentation<R>(
        self,
        edit: impl FnOnce(&mut S) -> R,
    ) -> Result<(Self, R), ExecutionUpdateError> {
        let focused_branch = self.focused_branch;
        let goal = self
            .state
            .open_branches
            .get(focused_branch)
            .cloned()
            .ok_or(ExecutionUpdateError::NotFrontier)?;
        let ProofObligation::Frontier(frontier) = goal.obligation else {
            return Err(ExecutionUpdateError::NotFrontier);
        };
        let mut state = Arc::unwrap_or_clone(self.state);
        state.open_branches = state.open_branches.without_at(focused_branch);
        let ProofBranchState {
            facts,
            unfolded_predicates,
            execution,
        } = goal.state;
        let mut execution =
            Arc::unwrap_or_clone(execution.ok_or(ExecutionUpdateError::MissingExecution)?);
        let result = edit(&mut execution.presentation);
        state.open_branches = state.open_branches.insert_existing_at(
            focused_branch,
            ProofBranch::new(
                ProofObligation::Frontier(frontier),
                ProofBranchState {
                    facts,
                    unfolded_predicates,
                    execution: Some(Arc::new(execution)),
                },
            ),
        );
        Ok((Self::new(state, focused_branch), result))
    }

    /// Validate only retained evidence. Preparation, lowering, and proof
    /// discovery are deliberately absent from the closure boundary.
    pub(crate) fn validate_checked_invariant_lowerings(
        &self,
        checks: &[crate::kernel::CLoopInvariantCheck],
    ) -> Result<(), String> {
        let (branch, execution) = self
            .focused_frontier_execution()
            .map_err(|_| "invariant closure requires an execution frontier".to_string())?;
        if execution.core.frontier.region != super::ExecutionRegionKind::LoopBody {
            return Err("invariant closure requires a loop body".into());
        }
        let evidence = execution
            .core
            .checked_invariant_lowerings
            .as_ref()
            .ok_or("invariant closure is missing prepared lowering evidence")?;
        if !evidence.snapshot.shares_storage_with(&execution.core.state)
            || !evidence.facts.shares_premises_with(&branch.state.facts)
            || !evidence
                .effects
                .shares_storage_with(&execution.core.effect_facts)
        {
            return Err("invariant closure has stale lowering evidence".into());
        }
        if evidence.checks != checks {
            return Err(
                "invariant closure evidence belongs to a different invariant bundle".into(),
            );
        }
        if !evidence.body.as_ref().is_some_and(|body| body.recheck()) {
            return Err("invariant closure has missing or invalid body evidence".into());
        }
        Ok(())
    }

    /// Record the source closer request. This alone is not bundle authority;
    /// loop finalization separately validates the prepared lowerings above.
    pub(crate) fn request_frontier_invariant_closure(&self) -> Result<Self, ExecutionUpdateError> {
        let (branch, execution) = self.focused_frontier_execution()?;
        if execution.core.frontier.region != super::ExecutionRegionKind::LoopBody {
            return Err(ExecutionUpdateError::NotLoopBody);
        }
        if execution.core.region_invariants_close_requested {
            return Err(ExecutionUpdateError::InvariantsAlreadyClosed);
        }
        let mut core = execution.core.clone();
        core.region_invariants_close_requested = true;
        let state = ProofBranchState {
            facts: branch.state.facts.clone(),
            unfolded_predicates: branch.state.unfolded_predicates.clone(),
            execution: Some(Arc::new(ProofExecutionState::new(
                core,
                execution.presentation.clone(),
            ))),
        };
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .with_branch_state_at(self.focused_branch, state),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            self.focused_branch,
        ))
    }

    /// Publishes the result of a separately checked frontier transition while
    /// preserving every unrelated branch and the focused frontier's
    /// obligation and unfold set. The caller remains responsible for checking
    /// the semantic transition; replacing that checked-driver boundary with
    /// typed kernel evidence would be a separate interface redesign.
    pub(crate) fn publish_checked_frontier_transition(
        &self,
        facts: ProofFacts,
        execution: ProofExecutionState<S>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ExecutionUpdateError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ExecutionUpdateError::NotFrontier)?;
        if !matches!(branch.obligation, ProofObligation::Frontier(_)) {
            return Err(ExecutionUpdateError::NotFrontier);
        }
        if branch.state.execution.is_none() {
            return Err(ExecutionUpdateError::MissingExecution);
        }
        let open_branches =
            self.state
                .open_branches
                .replace_frontier_at(self.focused_branch, facts, execution);
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches,
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            },
            self.focused_branch,
        ))
    }

    /// Publishes two separately checked frontier successors as sibling proof
    /// branches. The checked driver supplies each arm's semantic result; the
    /// kernel preserves the current obligation and unfold state and owns the
    /// branch identities and split topology.
    pub(crate) fn publish_checked_frontier_split(
        &self,
        arms: [(ProofFacts, ProofExecutionState<S>); 2],
        introduced_facts: [Vec<Proposition>; 2],
        focused_checked_facts: Vec<Proposition>,
    ) -> Result<ProofSplit<L, ProofObligation<P, O>, ProofExecutionState<S>>, ExecutionUpdateError>
    {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ExecutionUpdateError::NotFrontier)?;
        let ProofObligation::Frontier(frontier) = &branch.obligation else {
            return Err(ExecutionUpdateError::NotFrontier);
        };
        if branch.state.execution.is_none() {
            return Err(ExecutionUpdateError::MissingExecution);
        }
        let unfolded_predicates = branch.state.unfolded_predicates.clone();
        let [then_arm, else_arm] = arms.map(|(facts, execution)| {
            ProofBranch::new(
                ProofObligation::Frontier(frontier.clone()),
                ProofBranchState {
                    facts,
                    unfolded_predicates: unfolded_predicates.clone(),
                    execution: Some(Arc::new(execution)),
                },
            )
        });
        let (split, branches, open_branches) = self
            .state
            .open_branches
            .split_at(self.focused_branch, [then_arm, else_arm]);
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(introduced_facts[0].clone()),
                    checked_facts: Arc::new(focused_checked_facts),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts,
        })
    }

    pub(crate) fn publish_checked_partial_frontier_split(
        &self,
        arms: [Option<(ProofFacts, Arc<ProofExecutionState<S>>)>; 2],
        introduced_facts: [Option<Vec<Proposition>>; 2],
    ) -> Result<(Self, super::SplitId, [Option<BranchId>; 2]), ExecutionUpdateError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ExecutionUpdateError::NotFrontier)?;
        let ProofObligation::Frontier(frontier) = &branch.obligation else {
            return Err(ExecutionUpdateError::NotFrontier);
        };
        if branch.state.execution.is_none() {
            return Err(ExecutionUpdateError::MissingExecution);
        }
        let focused_arm = arms
            .iter()
            .position(Option::is_some)
            .ok_or(ExecutionUpdateError::MissingExecution)?;
        let (split, reserved, mut open_branches) = self
            .state
            .open_branches
            .begin_split::<2>(self.focused_branch);
        let mut branch_ids = [None, None];
        for (index, arm) in arms.into_iter().enumerate() {
            let Some((facts, execution)) = arm else {
                continue;
            };
            branch_ids[index] = Some(reserved[index]);
            open_branches = open_branches.insert_existing_at(
                reserved[index],
                ProofBranch::new(
                    ProofObligation::Frontier(frontier.clone()),
                    ProofBranchState {
                        facts,
                        unfolded_predicates: branch.state.unfolded_predicates.clone(),
                        execution: Some(execution),
                    },
                ),
            );
        }
        let deltas = introduced_facts[focused_arm].clone().unwrap_or_default();
        Ok((
            Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(deltas.clone()),
                    checked_facts: Arc::new(deltas),
                },
                reserved[focused_arm],
            ),
            split,
            branch_ids,
        ))
    }

    /// Closes `split` by replacing its reserved arms with the joined parent
    /// branch. Every child must be an arm identity reserved by exactly this
    /// split (a decided split names its one feasible arm twice), and the
    /// parent must precede the split and be retired. All of this is checked
    /// here and in the branch store in every build profile.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn publish_reserved_checked_frontier_join(
        &self,
        split: super::SplitId,
        children: [BranchId; 2],
        parent: BranchId,
        facts: ProofFacts,
        unfolded_predicates: PersistentOrderedSet<String>,
        execution: ProofExecutionState<S>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ProofJoinError> {
        let valid_children = children
            .iter()
            .all(|child| split.reserves(*child, children.len()));
        if !valid_children
            || !split.follows(parent)
            || !self.state.open_branches.has_allocated(parent)
            || self.state.open_branches.get(parent).is_some()
        {
            return Err(ProofJoinError::InvalidSplit);
        }
        let branch = ProofBranch::new(
            ProofObligation::Frontier(FrontierObligation),
            ProofBranchState {
                facts,
                unfolded_predicates,
                execution: Some(Arc::new(execution)),
            },
        );
        let open_branches = self
            .state
            .open_branches
            .join_reserved_at(children, parent, branch)
            .ok_or(ProofJoinError::InvalidSplit)?;
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches,
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            },
            parent,
        ))
    }

    #[cfg(test)]
    pub(crate) fn split_frontier_cases(
        &self,
        disjunction: Proposition,
    ) -> Result<ProofSplit<L, ProofObligation<P, O>, ProofExecutionState<S>>, FrontierSplitError>
    {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(FrontierSplitError::Completed)?;
        let ProofObligation::Frontier(frontier) = &branch.obligation else {
            return Err(FrontierSplitError::NotFrontier);
        };
        let execution = branch
            .state
            .execution
            .clone()
            .ok_or(FrontierSplitError::MissingExecution)?;
        if !branch.state.facts.contains(&disjunction) {
            return Err(FrontierSplitError::MissingDisjunction(disjunction));
        }
        let Proposition::Or(left, right) = disjunction else {
            return Err(FrontierSplitError::ExpectedDisjunction(disjunction));
        };
        let introduced_facts = [vec![left.as_ref().clone()], vec![right.as_ref().clone()]];
        let arm = |disjunct: Proposition| {
            ProofBranch::new(
                ProofObligation::Frontier(frontier.clone()),
                ProofBranchState {
                    facts: branch.state.facts.with_fact(disjunct),
                    unfolded_predicates: branch.state.unfolded_predicates.clone(),
                    execution: Some(execution.clone()),
                },
            )
        };
        let (split, branches, open_branches) = self
            .state
            .open_branches
            .split_at(self.focused_branch, [arm(*left), arm(*right)]);
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(introduced_facts[0].clone()),
                    checked_facts: Arc::new(introduced_facts[0].clone()),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts,
        })
    }

    pub(crate) fn split_frontier_if(
        &self,
        then_fact: Proposition,
        else_fact: Proposition,
        presentations: [S; 2],
    ) -> Result<ProofSplit<L, ProofObligation<P, O>, ProofExecutionState<S>>, FrontierSplitError>
    {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(FrontierSplitError::Completed)?;
        let ProofObligation::Frontier(frontier) = &branch.obligation else {
            return Err(FrontierSplitError::NotFrontier);
        };
        let execution = branch
            .state
            .execution
            .as_ref()
            .ok_or(FrontierSplitError::MissingExecution)?;
        let negated_then = Proposition::Not(Box::new(then_fact.clone()));
        if else_fact != negated_then
            && !super::fact_reasoning::condition_polarity_forms(&negated_then).contains(&else_fact)
        {
            return Err(FrontierSplitError::NonComplementaryCases);
        }
        let introduced_facts = [vec![then_fact.clone()], vec![else_fact.clone()]];
        let partition = CheckedProofCasePartition::check(
            &branch.state.facts,
            then_fact.clone(),
            else_fact.clone(),
        )
        .expect("the checked complementary facts form a proof-case partition");
        let [then_presentation, else_presentation] = presentations;
        let arm = |arm_index: usize, fact: Proposition, presentation: S| {
            let facts = branch.state.facts.with_fact(fact);
            let mut core = execution.core.clone();
            assert!(core.record_proof_case_arm(partition.clone(), arm_index, facts.clone()));
            ProofBranch::new(
                ProofObligation::Frontier(frontier.clone()),
                ProofBranchState {
                    facts,
                    unfolded_predicates: branch.state.unfolded_predicates.clone(),
                    execution: Some(Arc::new(ProofExecutionState::new(core, presentation))),
                },
            )
        };
        let (split, branches, open_branches) = self.state.open_branches.split_at(
            self.focused_branch,
            [
                arm(0, then_fact, then_presentation),
                arm(1, else_fact, else_presentation),
            ],
        );
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(introduced_facts[0].clone()),
                    checked_facts: Arc::new(introduced_facts[0].clone()),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts,
        })
    }

    /// Duplicate the same obligation without introducing assumptions. Used
    /// to organize a checked constructor partition; only its leaves may
    /// introduce the kernel-issued constructor equations.
    pub(crate) fn split_frontier_match_group(
        &self,
    ) -> Result<ProofSplit<L, ProofObligation<P, O>, ProofExecutionState<S>>, FrontierSplitError>
    {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(FrontierSplitError::Completed)?;
        if !matches!(branch.obligation, ProofObligation::Frontier(_)) {
            return Err(FrontierSplitError::NotFrontier);
        }
        let (split, branches, open_branches) = self
            .state
            .open_branches
            .split_at(self.focused_branch, [branch.clone(), branch.clone()]);
        Ok(ProofSplit {
            proof: Self::new(
                ProofState {
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(vec![]),
                    checked_facts: Arc::new(vec![]),
                },
                branches[0],
            ),
            split,
            branches,
            introduced_facts: [vec![], vec![]],
        })
    }

    pub(crate) fn introduce_frontier_match_case(
        &self,
        partition: Arc<CheckedProofCasePartition>,
        index: usize,
    ) -> Result<Self, &'static str> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or("match requires an open branch")?;
        if !matches!(branch.obligation, ProofObligation::Frontier(_)) {
            return Err("match requires an execution frontier");
        }
        let case = partition
            .case_fact(index)
            .ok_or("match case index is outside its partition")?
            .clone();
        let mut execution = branch
            .state
            .execution
            .as_deref()
            .cloned()
            .ok_or("match requires execution state")?;
        let facts = branch.state.facts.with_fact(case.clone());
        if !execution
            .core
            .record_proof_case_arm(partition, index, facts.clone())
        {
            return Err("match witness scope or case premise is invalid");
        }
        let mut successor = branch.clone();
        successor.state.facts = facts;
        successor.state.execution = Some(Arc::new(execution));
        Ok(Self::new(
            ProofState {
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .replace_at(self.focused_branch, successor),
                added_facts: Arc::new(vec![case.clone()]),
                checked_facts: Arc::new(vec![case]),
            },
            self.focused_branch,
        ))
    }
}

impl<L, O, E> Deref for ProofObject<L, O, E> {
    type Target = ProofState<L, O, E>;

    fn deref(&self) -> &Self::Target {
        self.state()
    }
}

impl<P: Clone, O: Clone, E: Clone> ProofBranches<ProofBranch<ProofObligation<P, O>, E>> {
    #[cfg(test)]
    pub(crate) fn obligation(&self, at: BranchId) -> Option<&ProofObligation<P, O>> {
        Some(&self.get(at)?.obligation)
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

    pub(crate) fn is_discharged(&self) -> bool {
        self.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::PropositionObligation;
    use crate::kernel::{Bitvector32Term, Sort, Term, Variable};

    #[test]
    fn invariant_body_evidence_requires_exact_complete_root_and_context() {
        use crate::kernel::proof::{
            ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
        };
        use crate::kernel::{
            CComparisonOperator, CLoopInvariantCheck, CState, CValue, SpecExpression,
            SpecProposition,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let root = |facts: ProofFacts, core: ExecutionProofCore| -> TestProof {
            ProofObject::root(
                (),
                ProofBranch::new(
                    ProofObligation::Frontier(FrontierObligation),
                    ProofBranchState {
                        facts,
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                    },
                ),
            )
        };
        let checks = [0, 1].map(|value| {
            CLoopInvariantCheck::new(
                SpecProposition::Comparison {
                    left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))),
                    operator: CComparisonOperator::LessEqual,
                    right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))),
                },
                None,
                None,
            )
        });
        let entry = CState::new();
        let samples = [16, 32, 64, 128].map(|size| {
            let facts = ProofFacts::from_ordered(
                &(0..size)
                    .map(|i| Proposition::Predicate {
                        name: format!("unrelated_{i}"),
                        arguments: vec![],
                    })
                    .collect::<Vec<_>>(),
            );
            let core = ExecutionProofCore::at_entry(
                CState::new(),
                ExecutionFrontier {
                    region: ExecutionRegionKind::LoopBody,
                    position: FrontierPosition::RegionBoundary,
                    ..Default::default()
                },
            );
            let frontier = root(facts.clone(), core);
            let ((body, scope), opening_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    frontier
                        .open_invariant_body(&entry, &checks, |_| ())
                        .unwrap()
                });
            assert!(
                frontier
                    .retain_invariant_body(scope.clone(), &body)
                    .is_err()
            );
            // Even the same exact goal and premises in a fresh root are not this scope.
            let unrelated = TestProof::root((), body.state.open_branches.root_branch().clone())
                .apply_normalize()
                .ok()
                .unwrap();
            assert!(
                frontier
                    .retain_invariant_body(scope.clone(), &unrelated)
                    .is_err()
            );
            let complete = body.apply_normalize().ok().unwrap();
            let (closed, closing_work) = crate::instrumentation::measure_deterministic_work(|| {
                let closed = frontier
                    .retain_invariant_body(scope.clone(), &complete)
                    .unwrap();
                closed
                    .validate_checked_invariant_lowerings(&checks)
                    .unwrap();
                closed
            });
            assert!(
                closed
                    .validate_checked_invariant_lowerings(&checks[..1])
                    .is_err()
            );
            let core = closed.execution_view().unwrap().execution().core.clone();
            for variant in 0..4 {
                let mut changed = core.clone();
                let mut changed_facts = facts.clone();
                match variant {
                    0 => changed.state = CState::new().into(),
                    1 => changed.effect_facts = Vec::new().into(),
                    2 => {
                        changed_facts = facts.with_fact(Proposition::Predicate {
                            name: "other_arm".into(),
                            arguments: vec![],
                        })
                    }
                    _ => {
                        Arc::make_mut(changed.checked_invariant_lowerings.as_mut().unwrap()).body =
                            None
                    }
                }
                let stale = root(changed_facts, changed);
                assert!(stale.validate_checked_invariant_lowerings(&checks).is_err());
                if variant < 3 {
                    assert!(
                        stale
                            .retain_invariant_body(scope.clone(), &complete)
                            .is_err()
                    );
                }
            }
            let mut wrong = core;
            Arc::make_mut(wrong.checked_invariant_lowerings.as_mut().unwrap())
                .body
                .as_mut()
                .unwrap()
                .goal =
                Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
            assert!(
                root(facts, wrong)
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            opening_work + closing_work
        });
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
                "{samples:?}"
            );
        }
    }

    #[test]
    fn invariant_body_does_not_assume_provisional_read_safety() {
        use crate::kernel::proof::{
            ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
        };
        use crate::kernel::{
            CComparisonOperator, CLoopInvariantCheck, CState, CType, CValue, Pointer,
            PointerOffsetTerm, SpecExpression, SpecMemory, SpecProposition,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let load = SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::Value(CValue::Pointer(
                crate::kernel::CPointerValue::new(
                    Pointer {
                        block: "unallocated".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    CType::Int32Pointer,
                ),
            ))),
            value_type: CType::Int32,
        };
        // The value is reflexively equal, but evaluating it still requires a
        // read proof. No memory resource or safety premise is available.
        let checks = [CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: load.clone(),
                operator: CComparisonOperator::Equal,
                right: load,
            },
            None,
            None,
        )];
        let frontier = TestProof::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts: ProofFacts::default(),
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: Some(Arc::new(ProofExecutionState::new(
                        ExecutionProofCore::at_entry(
                            CState::new(),
                            ExecutionFrontier {
                                region: ExecutionRegionKind::LoopBody,
                                position: FrontierPosition::RegionBoundary,
                                ..Default::default()
                            },
                        ),
                        (),
                    ))),
                },
            ),
        );
        let (body, scope) = frontier
            .open_invariant_body(&CState::new(), &checks, |_| ())
            .unwrap();
        assert!(body.apply_normalize().is_err());
        assert!(
            body.apply_assumption(PropositionAssumptionContext::Pure)
                .is_err()
        );
        assert!(
            frontier
                .retain_invariant_body(scope.clone(), &body)
                .is_err()
        );
        // Proving the same goal under an extra assumption cannot fill this scope.
        let mut assumed = body.state.open_branches.root_branch().clone();
        let ProofObligation::Proposition(goal) = &assumed.obligation else {
            panic!("missing goal")
        };
        assumed.state.facts = assumed.state.facts.with_fact(goal.proposition().clone());
        let unrelated = TestProof::root((), assumed)
            .apply_assumption(PropositionAssumptionContext::Exact)
            .ok()
            .unwrap();
        assert!(frontier.retain_invariant_body(scope, &unrelated).is_err());
    }

    #[test]
    fn invariant_bundle_closure_checks_retained_evidence_and_context_locally() {
        use crate::kernel::proof::{
            ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
        };
        use crate::kernel::{
            CComparisonOperator, CLoopInvariantCheck, CState, CValue, SpecExpression,
            SpecProposition,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let root = |facts: ProofFacts, core: ExecutionProofCore| -> TestProof {
            ProofObject::root(
                (),
                ProofBranch::new(
                    ProofObligation::Frontier(FrontierObligation),
                    ProofBranchState {
                        facts,
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(ProofExecutionState::new(core, ()))),
                    },
                ),
            )
        };
        let checks = vec![
            CLoopInvariantCheck::new(
                SpecProposition::Comparison {
                    left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                    operator: CComparisonOperator::LessEqual,
                    right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                },
                None,
                None,
            ),
            CLoopInvariantCheck::new(
                SpecProposition::Predicate {
                    name: "invariant".into(),
                    arguments: vec![],
                },
                None,
                None,
            ),
        ];
        let mut samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let facts = ProofFacts::from_ordered(
                &(0..size)
                    .map(|i| Proposition::Predicate {
                        name: format!("unrelated_{i}"),
                        arguments: vec![],
                    })
                    .collect::<Vec<_>>(),
            )
            .with_fact(Proposition::Predicate {
                name: "invariant".into(),
                arguments: vec![Term::CState(CState::new())],
            });
            let core = ExecutionProofCore::at_entry(
                CState::new(),
                ExecutionFrontier {
                    region: ExecutionRegionKind::LoopBody,
                    position: FrontierPosition::RegionBoundary,
                    ..Default::default()
                },
            );
            let unprepared = root(facts.clone(), core);
            assert!(
                unprepared
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            let requested = unprepared
                .request_frontier_invariant_closure()
                .ok()
                .unwrap();
            assert!(
                requested
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            let (body, scope) = unprepared
                .open_invariant_body(&CState::new(), &checks, |_| ())
                .unwrap();
            let completed = body.apply_normalize().ok().unwrap();
            let prepared = unprepared.retain_invariant_body(scope, &completed).unwrap();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                prepared.validate_checked_invariant_lowerings(&checks)
            });
            result.unwrap();
            samples.push(work);
            assert!(prepared.validate_checked_invariant_lowerings(&[]).is_err());
            let changed_checks = vec![CLoopInvariantCheck::new(
                SpecProposition::Comparison {
                    left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
                    operator: CComparisonOperator::LessEqual,
                    right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(1))),
                },
                None,
                None,
            )];
            assert!(
                prepared
                    .validate_checked_invariant_lowerings(&changed_checks)
                    .is_err()
            );
            let core = prepared.execution_view().unwrap().execution().core.clone();
            let mut stale_effects = core.clone();
            stale_effects.effect_facts = Vec::new().into();
            assert!(
                root(facts.clone(), stale_effects)
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            let mut stale = core.clone();
            // Even an equal-valued replacement snapshot is not the saved one.
            stale.state = CState::new().into();
            assert!(
                root(facts.clone(), stale)
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            let other_facts = facts.with_fact(Proposition::Predicate {
                name: "other_arm".into(),
                arguments: vec![],
            });
            assert!(
                root(other_facts, core.clone())
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            let mut incomplete = core.clone();
            Arc::make_mut(incomplete.checked_invariant_lowerings.as_mut().unwrap()).body = None;
            assert!(
                root(facts.clone(), incomplete)
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            // A body for another judgment cannot certify this bundle.
            let mut incomplete = core.clone();
            Arc::make_mut(incomplete.checked_invariant_lowerings.as_mut().unwrap())
                .body
                .as_mut()
                .unwrap()
                .goal =
                Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
            assert!(
                root(facts.clone(), incomplete)
                    .validate_checked_invariant_lowerings(&checks)
                    .is_err()
            );
            prepared
                .validate_checked_invariant_lowerings(&checks)
                .unwrap();
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0].saturating_mul(2).saturating_add(8),
                "closure work: {samples:?}"
            );
        }
    }

    #[test]
    fn completed_proposition_retains_whether_it_relied_on_root_assumptions() {
        let truth = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true);
        for assumed in [false, true] {
            let branch = ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(truth.clone(), ())),
                ProofBranchState {
                    facts: ProofFacts::from_ordered(if assumed {
                        std::slice::from_ref(&truth)
                    } else {
                        &[]
                    }),
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            );
            let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
                ProofObject::root((), branch);
            let checked = proof
                .apply_normalize()
                .ok()
                .unwrap()
                .completed_proposition()
                .unwrap();
            assert_eq!(checked.is_closed(), !assumed);
            assert_eq!(checked.proposition(), &truth);
        }
    }

    #[test]
    fn intro_freshens_a_universal_binder_away_from_ambient_facts() {
        let binder = Variable(186);
        let body = Proposition::Predicate {
            name: "holds".to_string(),
            arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(binder))],
        };
        let goal = Proposition::ForAll {
            var: binder,
            sort: Sort::CInt32,
            body: Box::new(body.clone()),
        };
        let branch = ProofBranch::new(
            ProofObligation::Proposition(PropositionObligation::new(goal, ())),
            ProofBranchState {
                facts: ProofFacts::from_ordered(std::slice::from_ref(&body)),
                unfolded_predicates: PersistentOrderedSet::default(),
                execution: None,
            },
        );
        let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
            ProofObject::root((), branch);
        let mut introduced = None;

        let next = proof
            .apply_intro(|_, introduction| match introduction {
                PropositionIntroduction::Universal { variable } => {
                    introduced = Some(variable);
                }
                _ => panic!("expected universal introduction"),
            })
            .unwrap_or_else(|_| panic!("universal introduction should be accepted"));

        let introduced = introduced.expect("universal introduction should report its binder");
        assert_ne!(introduced, binder);
        let branch = next
            .state
            .open_branches
            .get(BranchId::ROOT)
            .expect("the introduced branch remains open");
        let ProofObligation::Proposition(obligation) = &branch.obligation else {
            panic!("universal introduction should retain a proposition goal");
        };
        assert_eq!(
            obligation.proposition(),
            &Proposition::Predicate {
                name: "holds".to_string(),
                arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(introduced))],
            }
        );
    }
}
