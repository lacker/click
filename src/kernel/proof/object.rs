//! Persistent checked proof-object state.
//!
//! Language-specific names and presentation records are opaque parameters.
//! The kernel owns the persistent state shape and never treats those
//! attachments as evidence.

use super::{
    BranchId, CheckedProofCasePartition, FrontierObligation, OutcomeProofState, ProofBranch,
    ProofBranchState, ProofBranches, ProofExecutionState, ProofObligation, PureFactStore,
};
#[cfg(test)]
use crate::kernel::CompareRelation;
use crate::kernel::primitives::first_unavailable_connective_side;
use crate::kernel::{Proposition, Sort, Variable};
use std::ops::Deref;
use std::sync::Arc;

/// The immutable state shared by checked proof successors. Its fields stay
/// private to the proof implementation so Source can inspect the state but
/// cannot assemble a whole semantic successor.
#[derive(Clone)]
pub(crate) struct ProofState<L, O, E> {
    pub(super) locals: L,
    pub(super) open_branches: ProofBranches<ProofBranch<O, E>>,
    pub(super) added_facts: Arc<Vec<Proposition>>,
    pub(super) checked_facts: Arc<Vec<Proposition>>,
    pub(super) termination: Option<Arc<crate::kernel::OrdinaryTerminationScope>>,
    pub(super) termination_root: bool,
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
/// Surface-language context and certificate lineage deliberately live
/// outside this handle. They may describe or render a checked derivation, but
/// they are not part of the semantic proof state and cannot change its focus.
#[derive(Clone)]
pub(crate) struct ProofObject<L, O, E> {
    pub(super) state: Arc<ProofState<L, O, E>>,
    pub(super) focused_branch: BranchId,
}

/// Borrowed authority that the focused goal is an execution frontier owning
/// checked execution state. Only the kernel can construct this view.
pub(crate) struct ProofExecutionView<'a, S> {
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

/// The inputs prepared once from one loop path for both the boundary
/// decision and the invariant proof. The latter can only open on that path.
pub(crate) struct PreparedLoopInvariantEdge {
    state: crate::kernel::ExecutionState,
    iteration_entry: crate::kernel::ExecutionState,
    head_iterations: crate::kernel::IntegerTerm,
    facts: PureFactStore,
    obligations: Vec<crate::kernel::ProofObligation>,
    binding: super::execution::CheckedLoopInvariantLowerings,
}

impl PreparedLoopInvariantEdge {
    pub(crate) fn state(&self) -> &crate::kernel::ExecutionState {
        &self.state
    }

    pub(crate) fn assumptions(&self) -> &crate::kernel::PureFactContext {
        self.facts.assumptions()
    }

    pub(crate) fn obligations(&self) -> &[crate::kernel::ProofObligation] {
        &self.obligations
    }
}

fn balanced_invariant_conjunction(mut members: Vec<Proposition>) -> Option<Proposition> {
    while members.len() > 1 {
        let mut level = Vec::with_capacity(members.len().div_ceil(2));
        let mut pairs = members.into_iter();
        while let Some(left) = pairs.next() {
            level.push(match pairs.next() {
                Some(right) => Proposition::And(Box::new(left), Box::new(right)),
                None => left,
            });
        }
        members = level;
    }
    members.pop()
}

/// Combine the obligation-guard prefix only when constructing the checked
/// proof root. The executable loop keeps the original indexed obligations.
fn group_wide_invariant_guards(
    proposition: &Proposition,
    introductions: &crate::kernel::LoweringIntroductions,
) -> Option<(Proposition, Arc<crate::kernel::LoweringIntroductions>)> {
    use crate::kernel::LoweringIntroduction::{ObligationGuard, PathFactGuard};

    let leading_facts = introductions
        .iter()
        .take_while(|kind| **kind == PathFactGuard)
        .count();
    let guard_count = introductions[leading_facts..]
        .iter()
        .take_while(|kind| **kind == ObligationGuard)
        .count();
    if guard_count < 2 {
        return None;
    }
    let mut body = proposition;
    let mut heads = Vec::with_capacity(leading_facts + guard_count);
    for _ in 0..(leading_facts + guard_count) {
        let Proposition::Implies(antecedent, consequent) = body else {
            return None;
        };
        heads.push(antecedent.as_ref());
        body = consequent;
    }
    let mut guards = heads.split_off(leading_facts);
    // The same antecedent can be used for every repeated guard.
    guards.dedup();
    let combined = balanced_invariant_conjunction(guards.into_iter().cloned().collect())?;
    let goal = heads.into_iter().rev().fold(
        Proposition::Implies(Box::new(combined), Box::new(body.clone())),
        |body, fact| Proposition::Implies(Box::new(fact.clone()), Box::new(body)),
    );
    let adjusted = introductions[..leading_facts]
        .iter()
        .cloned()
        .chain(std::iter::once(ObligationGuard))
        .chain(introductions[leading_facts + guard_count..].iter().cloned())
        .collect();
    Some((goal, Arc::new(adjusted)))
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
    MissingDisjunction,
    ExpectedDisjunction,
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
    NonComplementaryCases,
}

pub(crate) enum ExecutionUpdateError {
    NotFrontier,
    MissingExecution,
    NotLoopBody,
    InvariantsAlreadyClosed,
}

#[derive(Clone, Copy)]
pub(crate) enum PropositionKnownContext {
    Exact,
    Pure,
    Materialized,
}

pub(crate) enum PropositionCloseError {
    NotProposition,
    Unavailable,

    ExpectedIntroduction(Proposition),
    IntegerFresheningExhausted,
    /// No witness is left above the witnesses already in scope
    /// ([`crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_LIMIT`]). The
    /// introduction refuses rather than reusing one: a variable of another
    /// origin is some other producer's, and a witness that names a live C
    /// variable is the capture the witness origin exists to prevent.
    UniversalWitnessFresheningExhausted,
    IntegerChoiceSourceUnavailable,
    IntegerChoiceWrongSort,
    IntegerChoiceFresheningExhausted,
    /// The goal is a conjunction or disjunction, and this side of it is the
    /// first one that no fact supplies.
    UnavailableSide(Proposition),
    ExpectedFiniteUniversal,
    MissingFiniteInstance,
    /// An explicit premise of a guarded induction application is not held.
    InductionPremiseUnavailable(Proposition),
    InstantiateQuantifiedUnavailable,
    InstantiateInvalid(super::fact_reasoning::ForallInstantiationError),
}

#[derive(Clone)]
pub(crate) enum PropositionIntroduction {
    Implication,
    /// A universal introduction reports the exact kernel variable it bound
    /// the body to, and the pointee type when the binder ranges over
    /// pointers, so a caller's presentation names the same value the
    /// checked goal now mentions.
    Universal {
        variable: crate::kernel::Variable,
        pointer: Option<crate::kernel::ProgramType>,
        object_class: Option<crate::kernel::effective_type::CAccessClass>,
        algebraic: Option<crate::kernel::AlgebraicType>,
    },
}

impl<'a, S> ProofExecutionView<'a, S> {
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
                termination: None,
                termination_root: false,
                locals,
                open_branches: ProofBranches::root(branch),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            BranchId::ROOT,
        )
    }

    pub(super) fn new(state: ProofState<L, O, E>, focused_branch: BranchId) -> Self {
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
        if self.state.open_branches.get(self.focused_branch).is_none() {
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
                    locals: self.state.locals.clone(),
                    open_branches,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                },
                ids.first().copied().unwrap_or(self.focused_branch),
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
        facts: PureFactStore,
    ) -> Result<Self, ProofFocusError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ProofFocusError::NotOpen)?;
        let state = ProofBranchState {
            facts,
            execution: branch.state.execution.clone(),
        };
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
        facts: PureFactStore,
        execution: Option<Arc<E>>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Result<Self, ProofFocusError> {
        self.state
            .open_branches
            .get(self.focused_branch)
            .ok_or(ProofFocusError::NotOpen)?;
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.replace_at(
                    self.focused_branch,
                    ProofBranch::new(obligation, ProofBranchState { facts, execution }),
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
        Some(ProofExecutionView { execution })
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
    fn completed_outcome_identity(&self) -> Result<&super::OutcomeIdentity, String> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or_else(|| "the outcome branch is no longer open".to_string())?;
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            return Err("completion requires a function outcome".into());
        };
        match outcome.first_open_goal()? {
            Some(super::OutcomeGoal::Claim { key, .. }) => {
                return Err(format!("outcome still owes contract claim {key:?}"));
            }
            Some(super::OutcomeGoal::Closing(goal)) => {
                return Err(format!(
                    "outcome still owes contract closing: {}",
                    goal.description()
                ));
            }
            None => {}
        }
        Ok(&outcome.data.core.identity)
    }

    /// Install the same outcome's checked return publication before closing.
    /// The producer already established its program-state correspondence.
    pub(crate) fn bind_outcome_publication(
        &self,
        publication: Arc<crate::kernel::PublishedFunctionOutcome>,
    ) -> Result<Self, String> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or("the outcome is no longer open")?;
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            return Err("publication requires a function outcome".into());
        };
        if !outcome
            .data
            .core
            .publication
            .as_ref()
            .is_some_and(|original| publication.belongs_to(original))
        {
            return Err("the publication belongs to another function outcome".into());
        }
        if outcome
            .data
            .core
            .publication
            .as_ref()
            .is_some_and(|current| Arc::ptr_eq(current, &publication))
        {
            return Ok(self.clone());
        }
        let mut outcome = outcome.clone();
        let mut data = outcome.data.as_ref().clone();
        data.core.publication = Some(publication);
        outcome.data = Arc::new(data);
        self.replace_focused_obligation(ProofObligation::FunctionOutcome(outcome))
            .map_err(|_| "the outcome is no longer open".into())
    }

    /// Publish only the checked evidence retained by this exact ordinary goal.
    /// No caller-supplied completion, specification, or path can be substituted.
    pub(crate) fn published_contract_claim(
        &self,
        key: &crate::kernel::FunctionContractClaimKey,
    ) -> Option<crate::kernel::CheckedFunctionProposition> {
        let branch = self.state.open_branches.get(self.focused_branch)?;
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            return None;
        };
        let super::ClaimGoalEvidence::Proposition(completion) =
            outcome.claims.as_ref()?.evidence(key)?
        else {
            return None;
        };
        let publication = outcome
            .data
            .core
            .publication
            .as_ref()
            .expect("a checked function outcome retains its producer publication");
        Some(publication.publish_claim(completion))
    }

    pub(crate) fn open_contract_execution(
        &self,
        execution: crate::kernel::CheckedFunctionExecution,
        whole: Option<&crate::kernel::WholeContractRoot>,
        branches: impl Iterator<Item = BranchId>,
    ) -> Result<crate::kernel::ContractExecutionOwner, String> {
        let mut outcomes = Vec::new();
        for id in branches {
            let branch = self
                .state
                .open_branches
                .get(id)
                .ok_or("an outcome branch was not opened")?;
            let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
                return Err("execution ownership requires function outcomes".into());
            };
            let publication = outcome
                .data
                .core
                .publication
                .as_ref()
                .ok_or("execution outcome has no producer publication")?;
            outcomes.push((
                outcome.path_index,
                outcome.data.core.identity.clone(),
                publication.clone(),
            ));
        }
        crate::kernel::ContractExecutionOwner::open(
            execution,
            whole.map(|root| root.plan()),
            outcomes,
        )
        .map(|owner| owner.bind_root(whole))
    }

    pub(crate) fn complete_function_outcome_in_execution(
        &self,
        owner: &Self,
        execution: &mut crate::kernel::ContractExecutionOwner,
    ) -> Result<Self, String> {
        let identity = self.completed_outcome_identity()?;
        let next = self.close_owned_outcome(owner, identity)?;
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .expect("the completed outcome is open");
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            unreachable!()
        };
        execution.finish_outcome(
            outcome.path_index,
            identity,
            outcome.claims.as_ref(),
            outcome.closing.as_ref(),
            outcome.data.core.publication.as_ref(),
        )?;
        Ok(next)
    }

    pub(crate) fn refute_function_outcome_in_execution(
        &self,
        owner: &Self,
        fact: &Proposition,
        execution: &mut crate::kernel::ContractExecutionOwner,
    ) -> Result<Self, String> {
        let next = self.refute_function_outcome_with_contract_in(owner, fact, None)?;
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .expect("the refuted outcome is open");
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            unreachable!()
        };
        execution.finish_outcome(
            outcome.path_index,
            &outcome.data.core.identity,
            None,
            None,
            None,
        )?;
        Ok(next)
    }

    pub(crate) fn finish_contract_execution(
        &self,
        execution: crate::kernel::ContractExecutionOwner,
    ) -> Result<crate::kernel::CompletedContractExecution, String> {
        if !self.is_complete() {
            return Err("ordinary outcome proof still has open obligations".into());
        }
        execution.finish()
    }

    /// Retire the outcome branch only after every source and closing goal is closed.
    #[cfg(test)]
    pub(crate) fn complete_function_outcome(&self) -> Result<Self, String> {
        self.completed_outcome_identity()?;
        Ok(self.closed_focused())
    }

    /// Return this case's completion to its owner without importing the case's
    /// local names, facts or presentation into its siblings. The only read is
    /// the selected branch and its generative outcome identity.
    #[cfg(test)]
    pub(crate) fn complete_function_outcome_in(&self, owner: &Self) -> Result<Self, String> {
        self.complete_function_outcome_with_contract_in(owner, None)
    }

    #[cfg(test)]
    pub(crate) fn complete_function_outcome_with_contract_in(
        &self,
        owner: &Self,
        progress: Option<&mut crate::kernel::ContractProofProgress>,
    ) -> Result<Self, String> {
        let identity = self.completed_outcome_identity()?;
        let next = self.close_owned_outcome(owner, identity)?;
        if let Some(progress) = progress {
            let branch = self
                .state
                .open_branches
                .get(self.focused_branch)
                .expect("completed outcome is open");
            let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
                unreachable!()
            };
            *progress = progress.finish_outcome(
                outcome.path_index,
                identity,
                outcome.claims.as_ref(),
                outcome.closing.as_ref(),
            )?;
        }
        Ok(next)
    }

    #[cfg(test)]
    pub(crate) fn refute_function_outcome_in(
        &self,
        owner: &Self,
        fact: &Proposition,
    ) -> Result<Self, String> {
        self.refute_function_outcome_with_contract_in(owner, fact, None)
    }

    pub(crate) fn refute_function_outcome_with_contract_in(
        &self,
        owner: &Self,
        fact: &Proposition,
        progress: Option<&mut crate::kernel::ContractProofProgress>,
    ) -> Result<Self, String> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or_else(|| "the outcome case is no longer open".to_string())?;
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            return Err("refutation requires an outcome case".into());
        };
        if !branch.state.facts.contradicts(fact) {
            return Err("the retained case contradiction was not available".into());
        }
        let next = self.close_owned_outcome(owner, &outcome.data.core.identity)?;
        if let Some(progress) = progress {
            *progress = progress.finish_outcome(
                outcome.path_index,
                &outcome.data.core.identity,
                None,
                None,
            )?;
        }
        Ok(next)
    }

    fn close_owned_outcome(
        &self,
        owner: &Self,
        identity: &super::OutcomeIdentity,
    ) -> Result<Self, String> {
        let branch = owner
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or_else(|| "the owner no longer has this outcome case open".to_string())?;
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            return Err("the selected owner branch is not an outcome case".into());
        };
        if !outcome.data.core.identity.same_as(identity) {
            return Err("the completion belongs to another outcome owner".into());
        }
        Ok(owner
            .focus_open_branch(self.focused_branch)
            .map_err(|_| "the owner no longer has this outcome case open".to_string())?
            .closed_focused())
    }

    /// Open the contract judgment on this branch. Its requirements, facts,
    /// outcome identity and execution all come from this same checked branch;
    /// no separately supplied context can reuse a domain-discharge receipt.
    pub(crate) fn focus_contract_claim(
        &self,
        goal: &crate::kernel::ContractClaimGoal,
        presentation: P,
    ) -> Result<Self, Vec<crate::kernel::ProofObligation>> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("focus_contract_claim");
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or_else(Vec::new)?;
        let outcome = match &branch.obligation {
            ProofObligation::FunctionOutcome(outcome) => Some(outcome.data.clone()),
            ProofObligation::Frontier(_) => None,
            _ => return Err(Vec::new()),
        };
        let pending = goal.unproved_requirements(branch.state.facts.assumptions());
        if !pending.is_empty() {
            return Err(pending);
        }
        let mut state = branch.state.clone();
        if outcome.is_none() {
            state.execution = None;
        }
        Ok(Self::root(
            self.state.locals.clone(),
            ProofBranch::new(
                ProofObligation::Proposition(super::PropositionObligation::for_claim_goal(
                    goal,
                    presentation,
                    outcome,
                )),
                state,
            ),
        ))
    }

    /// Open a source-only clause on its existing outcome cell. The selected
    /// key travels with the semantic proposition root through ordinary proof.
    pub(crate) fn focus_source_contract_claim(
        &self,
        key: &crate::kernel::FunctionContractClaimKey,
        proposition: Proposition,
        presentation: P,
    ) -> Result<Self, String> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or("source clause requires an open outcome")?;
        let ProofObligation::FunctionOutcome(outcome) = &branch.obligation else {
            return Err("source clause requires a function outcome".into());
        };
        let claims = outcome
            .claims
            .as_ref()
            .ok_or("outcome has no declared claim cells")?;
        claims.require_source_claim(key)?;
        Ok(Self::root(
            self.state.locals.clone(),
            ProofBranch::new(
                ProofObligation::Proposition(super::PropositionObligation::for_source_claim(
                    proposition,
                    presentation,
                    outcome.data.clone(),
                    key.clone(),
                )),
                branch.state.clone(),
            ),
        ))
    }

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
            self.state.open_branches.root_branch().state.facts.clone(),
            goal.outcome.as_deref().map(|outcome| outcome.core.clone()),
            goal.claim().cloned(),
            goal.source_claim().cloned(),
        ))
    }

    /// Closes the focused proposition goal when the step that produced this
    /// state added it as a fact. A goal that was already available before
    /// the step stays open; only `known` closes that. The match is
    /// exact: a planned step sequence relies on the goal staying open after
    /// a step that adds it under another spelling, and the written-script
    /// runner closes that case with a recorded `known` instead.
    pub(crate) fn closed_if_goal_was_added(&self) -> Option<Self> {
        let (goal, _) = self.focused_proposition()?;
        self.state
            .added_facts
            .contains(goal.proposition())
            .then(|| self.closed_focused())
    }

    fn focused_proposition(
        &self,
    ) -> Option<(
        &super::PropositionObligation<P, Arc<OutcomeProofState<S>>>,
        &PureFactStore,
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.close_at(self.focused_branch),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            self.focused_branch,
        )
    }

    pub(crate) fn apply_known(
        &self,
        context: PropositionKnownContext,
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        if facts.holds_false() {
            return Ok(self.closed_focused());
        }
        let proposition = goal.proposition();
        let available = |proposition: &Proposition| {
            // Re-lowering a quoted quantified fact freshens its binders.
            // Its exact typed identity already has a persistent index,
            // including memory-reading forms outside the older equivalence
            // index. This recognizes the held fact without any search.
            if matches!(
                proposition,
                Proposition::ForAll { .. } | Proposition::Exists { .. } | Proposition::Implies(..)
            ) && facts.contains_quantified_identity(proposition)
            {
                return true;
            }
            if let Some(outcome) = goal.outcome.as_deref() {
                facts.pure_known_available(proposition)
                    || facts.available_across_effects(proposition, &*outcome.core.effect_facts)
            } else {
                match context {
                    PropositionKnownContext::Exact => {
                        // Instantiation can expose an inner universal whose retained
                        // binder differs from the goal's independently lowered binder.
                        // Alpha-equivalence preserves the exact fact; use the indexed
                        // quantified lookup without invoking a derivation search.
                        facts.available(proposition) || facts.quantified_fact_available(proposition)
                    }
                    PropositionKnownContext::Pure => facts.pure_known_available(proposition),
                    PropositionKnownContext::Materialized => {
                        // Alpha-equivalent quantified and Integer facts remain
                        // materialized when their exact state-aware keys match.
                        // This does not admit cross-effect transport.
                        facts.pure_known_available(proposition)
                    }
                }
            }
        };
        // The goal under another spelling of the same order claim (`0 <= e`
        // for the goal `e >= 0`, over machine or `Integer` operands) is an
        // available fact: a fixed set of exact lookups, one per spelling,
        // with no derivation or transport. The spellings include an equality
        // or disequality's mirrored orientation (`b != a` for `a != b`).
        let spelled_otherwise = || {
            super::fact_reasoning::order_claim_forms(proposition)
                .iter()
                .any(|form| form != proposition && facts.contains(form))
        };
        // A native comparison is the Integer comparison of its operands'
        // exact observations, so a goal whose Integer reading is available,
        // such as one the Integer equality closure derives, is too: at most
        // one lookup per reading.
        let observed_otherwise = || {
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                proposition,
            )
            .iter()
            .any(&available)
        };
        // Query the existing compound comparison index once per maximal
        // disjunction under the goal's conjunction spine. These selected
        // clauses are disjoint: nested connective traversal must not rebuild
        // a key for every overlapping prefix of a growing goal.
        let mut compound_available = std::collections::HashSet::new();
        let mut selected = vec![proposition];
        while let Some(part) = selected.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match part {
                Proposition::And(left, right) => {
                    selected.push(right);
                    selected.push(left);
                }
                Proposition::Or(..) if facts.assumptions().contains_proposition_fact(part) => {
                    compound_available.insert(std::ptr::from_ref(part));
                }
                _ => {}
            }
        }
        if compound_available.contains(&std::ptr::from_ref(proposition))
            || available(proposition)
            || crate::kernel::spec::sequence_membership_view(proposition)
                .as_ref()
                .is_some_and(&available)
            || spelled_otherwise()
            || observed_otherwise()
        {
            return Ok(self.closed_focused());
        }
        let bridge_available = |goal: &Proposition| {
            if super::fact_reasoning::known_uint32_from_defined_bytes(goal, |byte| {
                facts.contains(byte)
            }) || super::fact_reasoning::known_shifted_one(goal, &|bound| facts.contains(bound))
            {
                return true;
            }
            super::fact_reasoning::known_bridge_leaf(goal, &|premise| {
                // Adjacent footprint bounds use the exact endpoint order
                // in this context.
                if matches!(goal, Proposition::ResourceSeparate { .. })
                    && matches!(premise, Proposition::ConditionIs(..))
                {
                    facts.pure_known_available(premise)
                } else {
                    available(premise)
                }
            })
        };
        if super::fact_reasoning::computes_leaf(proposition)
            || super::arithmetic_special::known_pointer_alignment(proposition, facts.assumptions())
            || bridge_available(proposition)
            || crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                proposition,
            )
            .iter()
            .any(bridge_available)
        {
            return Ok(self.closed_focused());
        }
        // An implication whose consequent is an available fact holds
        // whatever its antecedent: one lookup of the consequent, as a guarded
        // requirement (`left implies requirement`) needs once its
        // requirement is known.
        let consequent_available = |side: &Proposition| {
            matches!(side, Proposition::Implies(_, consequent)
                if available(consequent) || facts.contains(consequent))
        };
        if consequent_available(proposition) {
            return Ok(self.closed_focused());
        }
        // A conjunction or disjunction that is not itself a fact still
        // follows from checked leaves: every conjunct, or one disjunct.
        // Each side uses indexed facts or goal-local computation, without
        // derivation search.
        if !matches!(proposition, Proposition::And(..) | Proposition::Or(..)) {
            return Err(PropositionCloseError::Unavailable);
        }
        let side_available = |side: &Proposition| {
            compound_available.contains(&std::ptr::from_ref(side))
                || available(side)
                || consequent_available(side)
                || facts.contains(side)
                || super::fact_reasoning::order_claim_forms(side)
                    .iter()
                    .any(|form| facts.contains(form))
                || super::fact_reasoning::computes_leaf(side)
                || super::arithmetic_special::known_pointer_alignment(side, facts.assumptions())
                || bridge_available(side)
        };
        match first_unavailable_connective_side(proposition, &side_available) {
            None => Ok(self.closed_focused()),
            Some(missing) => Err(PropositionCloseError::UnavailableSide(missing.clone())),
        }
    }

    /// Dev-only `sorry`: closes the focused proposition goal as admitted,
    /// without checking it against available facts.
    ///
    /// Returns `None` when the flag is off or the focused goal is not a
    /// proposition. This is the ONLY kernel operation that closes a goal
    /// without derivation — hence the name. The surface layer records an
    /// admission for every use; admitted results never verify in the gate.
    pub(crate) fn admit_focused_proposition_for_sorry(&self) -> Option<Self> {
        if !crate::kernel::sorry::sorry_is_allowed() {
            return None;
        }
        self.focused_proposition()?;
        Some(self.closed_focused())
    }

    /// An interface leaf uses indexed premises, pointer congruence, direct
    /// intrinsic facts, or an exact kernel-issued load definition; it never
    /// selects a derivation.
    pub(super) fn apply_interface_leaf(
        &self,
        definition: Option<&super::execution::CheckedInterfaceLoadDefinition>,
        read_premise: Option<&Proposition>,
    ) -> Option<Self> {
        let (goal, facts) = self.focused_proposition()?;
        (super::execution::checked_branch_fact_is_available(facts, goal.proposition())
            || super::execution::checked_interface_pointer_equality(facts, goal.proposition())
            || definition
                .is_some_and(|definition| definition.matches_goal_exactly(goal.proposition()))
            || read_premise.is_some_and(|premise| {
                facts.contains(premise)
                    && super::execution::interface_read_is_subrange(goal.proposition(), premise)
            }))
        .then(|| self.closed_focused())
    }

    /// Allocate a logical choice witness outside every execution, load and
    /// binder producer's namespace. Facts reserve earlier witnesses; the
    /// current goal and source body can also name witnesses not yet facts.
    pub(crate) fn fresh_existential_witness(
        &self,
        body: &Proposition,
        hint: Variable,
    ) -> Result<Variable, PropositionCloseError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionCloseError::NotProposition)?;
        let mut excluded = crate::kernel::proposition_variables(body);
        if let ProofObligation::Proposition(goal) = &branch.obligation {
            excluded.extend(crate::kernel::proposition_variables(goal.proposition()));
        }
        // A slice's count names its slice: the witness's count is fresh too.
        let counted = excluded
            .iter()
            .filter_map(Variable::counted_slice)
            .collect::<Vec<_>>();
        excluded.extend(counted);
        let fresh = branch
            .state
            .facts
            .fresh_universal_witness(&excluded)
            .ok_or(PropositionCloseError::IntegerChoiceFresheningExhausted)?;
        let variable = if hint.is_witness() && hint.0 > fresh.0 {
            hint
        } else {
            fresh
        };
        if variable.0 >= crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_LIMIT {
            return Err(PropositionCloseError::IntegerChoiceFresheningExhausted);
        }
        Ok(variable)
    }

    /// Checks and instantiates an Integer existential fact for a checked proof
    /// transition. The returned witness proposition is the only fact the
    /// surface driver may publish; freshness is checked against the complete
    /// kernel fact index before substitution.
    pub(crate) fn check_integer_exists_choice(
        &self,
        source: &Proposition,
        hint: Variable,
    ) -> Result<(Proposition, Variable), PropositionCloseError> {
        let (_, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        if !facts.contains_top_level(source) {
            return Err(PropositionCloseError::IntegerChoiceSourceUnavailable);
        }
        let Proposition::Exists {
            var,
            sort: Sort::Integer,
            body,
            ..
        } = source
        else {
            return Err(PropositionCloseError::IntegerChoiceWrongSort);
        };
        let variable = self.fresh_existential_witness(body, hint)?;
        let witness = crate::kernel::IntegerTerm::var(variable);
        let fact = super::super::reasoning::substitute_integer_variable_in_pure_proposition(
            body, **var, &witness,
        )
        .map_err(|_| PropositionCloseError::IntegerChoiceFresheningExhausted)?;
        Ok((fact, variable))
    }

    /// Opens exactly the stated, available existential. Each binder adds a
    /// fresh variable and its instantiated body; no requirement index or
    /// search for an implied existential is involved.
    pub(crate) fn check_exists_bindings(
        &self,
        source: &Proposition,
        count: usize,
        hint: Variable,
    ) -> Result<Vec<(Proposition, Variable, Sort)>, PropositionCloseError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionCloseError::NotProposition)?;
        let facts = &branch.state.facts;
        // Lowering a written binder gives it a different internal identity
        // from an otherwise identical established fact. Select the retained
        // fact through the kernel's indexed, alpha-checked quantified lookup;
        // do not loosen the older index-addressed `choose` rule above.
        // Each leaf conjunct of a fact is itself an available fact, so an
        // existential held as one conjunct of a requirement opens as one held
        // alone does.
        let available =
            if facts.contains_top_level(source) || facts.contains_proper_conjunct(source) {
                source.clone()
            } else if let Some(conjunct) = facts.alpha_equivalent_proper_conjunct(source) {
                conjunct
            } else {
                facts
                    .matching_quantified_fact(source)
                    .ok_or(PropositionCloseError::IntegerChoiceSourceUnavailable)?
            };
        let mut current = available;
        let mut next = hint;
        let mut opened = Vec::with_capacity(count);
        for _ in 0..count {
            let Proposition::Exists {
                var, sort, body, ..
            } = current
            else {
                return Err(PropositionCloseError::IntegerChoiceWrongSort);
            };
            if !matches!(
                sort,
                Sort::Integer
                    | Sort::ProgramInt32
                    | Sort::ProgramInt64
                    | Sort::ProgramInteger(_)
                    | Sort::ProgramPointer(_)
                    | Sort::ProgramObjectPointer(_, _)
                    | Sort::Algebraic(_)
            ) {
                return Err(PropositionCloseError::IntegerChoiceWrongSort);
            }
            let chosen = self.fresh_existential_witness(&body, next)?;
            current = match &sort {
                Sort::Integer => {
                    super::super::reasoning::substitute_integer_variable_in_pure_proposition(
                        &body,
                        *var,
                        &crate::kernel::IntegerTerm::var(chosen),
                    )
                    .map_err(|_| PropositionCloseError::IntegerChoiceFresheningExhausted)?
                }
                Sort::ProgramInt32 | Sort::ProgramInt64 | Sort::ProgramInteger(_) => {
                    crate::kernel::substitute_int32_variable_in_proposition(
                        &body,
                        *var,
                        crate::kernel::OldMachineTerm::Variable(chosen),
                    )
                }
                Sort::ProgramPointer(program_type)
                | Sort::ProgramObjectPointer(program_type, _) => {
                    let pointer =
                        if matches!(program_type, crate::kernel::ProgramType::FunctionPointer(_)) {
                            crate::kernel::Address::symbolic_function(chosen)
                        } else {
                            crate::kernel::Address::symbolic(chosen)
                        };
                    let body =
                        crate::kernel::quantifiers::rename_slice_count(&body, *var, chosen, &sort);
                    crate::kernel::substitute_pointer_variable_in_proposition(&body, *var, &pointer)
                }
                Sort::Algebraic(algebraic_type) => {
                    super::super::reasoning::substitute_algebraic_variable_in_proposition(
                        &body,
                        *var,
                        &crate::kernel::AlgebraicTerm {
                            algebraic_type: algebraic_type.clone(),
                            node: crate::kernel::AlgebraicTermNode::Variable(chosen),
                        },
                    )
                }
                _ => unreachable!("checked above"),
            };
            opened.push((current.clone(), chosen, sort));
            next = Variable::witness(
                chosen
                    .0
                    .checked_add(1)
                    .ok_or(PropositionCloseError::IntegerChoiceFresheningExhausted)?,
            );
        }
        Ok(opened)
    }

    pub(crate) fn apply_close_bounds(&self, premises: &[Proposition]) -> Result<Self, String> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or("checked bounds require a proposition goal")?;
        if !super::arithmetic_special::checks_selected_float_bounds(goal.proposition(), premises)
            && !super::arithmetic_special::checks_signed_product_guards(
                goal.proposition(),
                premises,
            )
        {
            return Err(
                "the cited bounds do not establish the goal by a checked bound rule".into(),
            );
        }
        for (index, premise) in premises.iter().enumerate() {
            if !super::fact_reasoning::listed_condition_available(premise, facts) {
                return Err(format!("selected bound {index} is not exactly available"));
            }
        }
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_preserve(
        &self,
        separation: &Proposition,
        field: Option<crate::kernel::eval::typed_reads::FieldSelection>,
    ) -> Result<Self, String> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or("preserve requires a proposition goal")?;
        let return_state = goal.outcome.as_ref().and_then(|outcome| {
            (outcome.core.publication.is_some() && !outcome.core.is_exceptional)
                .then_some(&*outcome.core.state)
        });
        super::preservation::apply(separation, field, goal.proposition(), return_state, |p| {
            facts.contains(p)
        })?;
        Ok(self.closed_focused())
    }

    /// Introduces the head of the focused proposition goal.
    ///
    /// `presentation` derives the successor's opaque presentation from the
    /// checked introduction: its kind, and the exact fact the kernel added,
    /// when it added one. The callback chooses neither the kernel
    /// proposition nor the introduced fact.
    pub(crate) fn apply_intro(
        &self,
        presentation: impl FnOnce(&P, PropositionIntroduction, Option<&Proposition>) -> P,
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
            Proposition::ForAll {
                var, sort, body, ..
            } => {
                let (variable, body, pointer, algebraic) = match sort {
                    Sort::ProgramPointer(program_type)
                    | Sort::ProgramObjectPointer(program_type, _) => {
                        let (variable, body) = facts
                            .freshen_pointer_forall_body(**var, *program_type, body)
                            .ok_or(PropositionCloseError::UniversalWitnessFresheningExhausted)?;
                        (variable, body, Some(*program_type), None)
                    }
                    Sort::Integer => {
                        let (variable, body) = facts
                            .freshen_integer_forall_body(**var, body)
                            .ok_or(PropositionCloseError::IntegerFresheningExhausted)?;
                        (variable, body, None, None)
                    }
                    Sort::Algebraic(algebraic_type) => {
                        let (variable, body) = facts
                            .freshen_algebraic_forall_body(**var, algebraic_type, body)
                            .ok_or(PropositionCloseError::UniversalWitnessFresheningExhausted)?;
                        (variable, body, None, Some(algebraic_type.clone()))
                    }
                    _ => {
                        let (variable, body) = facts
                            .freshen_int32_forall_body(**var, body)
                            .ok_or(PropositionCloseError::UniversalWitnessFresheningExhausted)?;
                        (variable, body, None, None)
                    }
                };
                (
                    body,
                    None,
                    PropositionIntroduction::Universal {
                        variable,
                        pointer,
                        object_class: sort.pointer_object_class(),
                        algebraic,
                    },
                )
            }
            other => {
                return Err(PropositionCloseError::ExpectedIntroduction(other.clone()));
            }
        };
        let witness = match &introduction {
            PropositionIntroduction::Universal { variable, .. } => Some(*variable),
            _ => None,
        };
        let presentation = presentation(&goal.presentation, introduction, introduced.as_ref());
        let obligation = match goal.outcome.clone() {
            Some(outcome) => {
                super::PropositionObligation::at_outcome(proposition, presentation, outcome)
            }
            None => super::PropositionObligation::new(proposition, presentation),
        };
        // A universally introduced machine value has its declared type, whose
        // range is its format's: no bound is filed for it.
        let added_facts = introduced.into_iter().collect::<Vec<_>>();
        let mut facts = facts.clone().with_reserved_variables(witness);
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
            execution: branch.state.execution.clone(),
        };
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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

    /// Replaces the opaque presentation of the focused proposition goal.
    ///
    /// Presentation only: the checked proposition, its facts, the branch
    /// topology, and the focus are carried over unchanged, and the callback
    /// sees nothing but the presentation it is replacing. This is how a
    /// language-layer goal attaches the record of the lowering that produced
    /// it after the goal was constructed; it establishes no proposition and
    /// discharges nothing. `None` when the focused branch is not a
    /// proposition goal.
    pub(crate) fn with_focused_proposition_presentation(
        &self,
        presentation: impl FnOnce(&P) -> P,
    ) -> Option<Self>
    where
        L: Clone,
        S: Clone,
        P: Clone,
    {
        let branch = self.state.open_branches.get(self.focused_branch)?;
        let ProofObligation::Proposition(goal) = &branch.obligation else {
            return None;
        };
        let obligation = goal.with_presentation(presentation(&goal.presentation));
        Some(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.replace_at(
                    self.focused_branch,
                    ProofBranch::new(
                        ProofObligation::Proposition(obligation),
                        branch.state.clone(),
                    ),
                ),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn apply_enumerate(&self) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let Some(instances) =
            crate::kernel::finite_forall_goal_instances(goal.proposition(), false)
        else {
            return Err(PropositionCloseError::ExpectedFiniteUniversal);
        };
        for (_, instance) in instances {
            // The structural instance check, not the general prover: an
            // instance that is itself quantified is a further proof step.
            if !super::fact_reasoning::enumerated_instance_is_discharged(&instance, facts) {
                return Err(PropositionCloseError::MissingFiniteInstance);
            }
        }
        Ok(self.closed_focused())
    }

    pub(crate) fn close_unreachable_frontier(&self) -> Option<Self> {
        let branch = self.state.open_branches.get(self.focused_branch)?;
        (matches!(branch.obligation, ProofObligation::Frontier(_))
            && branch.state.facts.holds_false())
        .then(|| self.closed_focused())
    }

    /// Modus ponens with an explicitly selected implication and evidence.
    /// Only the written source and premises are visited; ambient facts are
    /// queried by exact keys to establish their availability.
    pub(crate) fn apply_fact(
        &self,
        fact: &Proposition,
        premises: &[Proposition],
    ) -> Result<Self, &'static str> {
        self.apply_implication(fact, Some(premises))
    }

    pub(crate) fn apply_fact_from_scope(&self, fact: &Proposition) -> Result<Self, &'static str> {
        self.apply_implication(fact, None)
    }

    fn apply_implication(
        &self,
        fact: &Proposition,
        premises: Option<&[Proposition]>,
    ) -> Result<Self, &'static str> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or("`apply(fact)` requires an open proof branch")?;
        let facts = &branch.state.facts;
        if !matches!(fact, Proposition::Implies(..)) {
            return Err("`apply(fact)` requires an implication fact");
        }
        if !facts.contains_quantified_identity(fact) {
            return Err("`apply(fact)` source implication is not an available fact");
        }
        let mut selected = crate::kernel::PureFactContext::new();
        for premise in premises.unwrap_or_default() {
            if !facts.listed_premise_available(premise, &[], true) {
                return Err("selected implication evidence contains an unavailable premise");
            }
            selected = selected.assume_proposition(premise.clone());
        }
        let mut conclusion = fact;
        while let Proposition::Implies(antecedent, consequent) = conclusion {
            if first_unavailable_connective_side(antecedent, &|side| {
                (if premises.is_some() {
                    selected.contains_known(side)
                } else {
                    facts.pure_known_available(side) || facts.assumptions().contains_known(side)
                }) || super::fact_reasoning::computes_leaf(side)
            })
            .is_some()
            {
                return Err("`apply(fact)` has an unproved antecedent");
            }
            conclusion = consequent;
        }
        let added = (!facts.contains_top_level(conclusion))
            .then(|| conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = facts.with_fact(conclusion.clone());
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .with_facts_at(self.focused_branch, facts),
                checked_facts: Arc::new(added.clone()),
                added_facts: Arc::new(added),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn apply_instantiate(
        &self,
        quantified: Proposition,
        argument: super::fact_reasoning::InstanceArgument,
    ) -> Result<(Self, Proposition), PropositionCloseError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionCloseError::NotProposition)?;
        let facts = &branch.state.facts;
        let quantified =
            if facts.contains(&quantified) || facts.assumptions().contains_known(&quantified) {
                quantified
            } else if let Some(available) = facts.matching_quantified_fact(&quantified) {
                available
            } else {
                return Err(PropositionCloseError::InstantiateQuantifiedUnavailable);
            };
        let conclusion = super::fact_reasoning::instantiate_universal(&quantified, &argument)
            .map_err(PropositionCloseError::InstantiateInvalid)?;
        let added_facts = (!facts.contains_top_level(&conclusion))
            .then(|| conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = facts.with_fact(conclusion.clone());
        Ok((
            Self::new(
                ProofState {
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
                    locals: self.state.locals.clone(),
                    open_branches: self
                        .state
                        .open_branches
                        .with_facts_at(self.focused_branch, facts),
                    checked_facts: Arc::new(added_facts.clone()),
                    added_facts: Arc::new(added_facts),
                },
                self.focused_branch,
            ),
            conclusion,
        ))
    }

    pub(crate) fn apply_induction_instance(
        &self,
        quantified: Proposition,
        argument: super::fact_reasoning::InstanceArgument,
        explicit_premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (_, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        for premise in explicit_premises {
            if !facts.listed_premise_available(premise, &[], true) {
                return Err(PropositionCloseError::InductionPremiseUnavailable(
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
        // A listed mathematical comparison may spell an in-range machine
        // guard. Check only its operation's exact range keys in the retained
        // context, then pass that checked consequence beside the listed fact.
        let mut premises_with_readings = explicit_premises.to_vec();
        for premise in explicit_premises {
            if let Some(native) = facts.shared_operation_reading(premise) {
                premises_with_readings.push(native);
            }
        }
        let conclusion = super::fact_reasoning::check_forall_instantiation(
            &quantified,
            &argument,
            &premises_with_readings,
        )
        .map_err(PropositionCloseError::InstantiateInvalid)?;
        let added_facts = (!facts.contains_top_level(&conclusion))
            .then(|| conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = facts.with_fact(conclusion);
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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

    /// Constructor exhaustion reduces a proposition to one universally
    /// quantified implication per constructor. Payloads remain bound until
    /// ordinary `intro` freshens them; no free case equation is admitted.
    pub(crate) fn refine_proposition_algebraic_match(
        &self,
        value: &crate::kernel::AlgebraicTerm,
        order: &[usize],
    ) -> Result<Self, &'static str> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or("match requires a proposition goal")?;
        let equality = Proposition::Equal(
            crate::kernel::Term::Algebraic(value.clone().into()),
            crate::kernel::Term::Algebraic(value.clone().into()),
        );
        let reserved = crate::kernel::proposition_variables(goal.proposition())
            .into_iter()
            .chain(crate::kernel::proposition_variables(&equality))
            .collect();
        let first = facts
            .fresh_universal_witness(&reserved)
            .ok_or("match has exhausted fresh universal witness identities")?;
        // Every witness from `first` up is fresh: it is above each witness the
        // state and the goal name.
        let mut next = first.0;
        let cases = crate::kernel::api::algebraic_constructor_case_equations(value, &mut || {
            let variable = Variable::witness(next);
            next += 1;
            variable
        })
        .ok_or("match requires a supported datatype with a nonempty constructor family")?;
        if order.len() != cases.len()
            || order
                .iter()
                .copied()
                .collect::<std::collections::BTreeSet<_>>()
                != (0..cases.len()).collect()
        {
            return Err("match must cover every constructor exactly once");
        }
        let obligations = order
            .iter()
            .map(|&index| {
                let (case, binders) = &cases[index];
                crate::instrumentation::record_deterministic_work(1 + binders.len());
                binders.iter().rev().try_fold(
                    Proposition::Implies(
                        Box::new(case.clone()),
                        Box::new(goal.proposition().clone()),
                    ),
                    |body, (var, sort)| {
                        crate::kernel::quantifiers::close_forall(
                            Default::default(),
                            *var,
                            sort.clone(),
                            &body,
                        )
                        .ok_or("a constructor field's quantifier does not close")
                    },
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        fn conjunction(items: &[Proposition]) -> Proposition {
            if let [only] = items {
                return only.clone();
            }
            let middle = items.len() / 2;
            Proposition::And(
                Box::new(conjunction(&items[..middle])),
                Box::new(conjunction(&items[middle..])),
            )
        }
        let mut refined =
            super::PropositionObligation::new(conjunction(&obligations), goal.presentation.clone());
        refined.outcome = goal.outcome.clone();
        self.replace_focused_obligation(ProofObligation::Proposition(refined))
            .map_err(|_| "match requires an open proposition goal")
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
        let sequence = crate::kernel::spec::retained_sequence_equality_view(goal.proposition());
        let Proposition::And(left, right) = sequence.as_ref().unwrap_or_else(|| goal.proposition())
        else {
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
        // Membership is by comparison form, so a written disjunction reading
        // stored cells finds the one over the values stored there, and each
        // written disjunct is equivalent to its stored-value form.
        if !branch.state.facts.contains(&disjunction) {
            return Err(PropositionSplitError::MissingDisjunction);
        }
        let disjunction =
            crate::kernel::spec::sequence_membership_view(&disjunction).unwrap_or(disjunction);
        let Proposition::Or(left, right) = disjunction else {
            return Err(PropositionSplitError::ExpectedDisjunction);
        };
        let arm = |disjunct: Proposition| {
            ProofBranch::new(
                ProofObligation::Proposition(goal.clone()),
                ProofBranchState {
                    facts: branch.state.facts.with_fact(disjunct),
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
    #[cfg(test)]
    pub(crate) fn open_invariant_body(
        &self,
        loop_entry: &crate::kernel::ExecutionState,
        iteration_entry: &crate::kernel::ExecutionState,
        head_iterations: &crate::kernel::IntegerTerm,
        checks: &[crate::kernel::LoopInvariantCheck],
        ranking_measures: &[crate::kernel::RankingComponent],
        binders: &[crate::kernel::LoopBinder],
        definitions: &[crate::kernel::CompositeResourceDefinition],
        presentation: impl FnOnce(
            &Proposition,
            &[Option<Arc<crate::kernel::LoweringIntroductions>>],
        ) -> P,
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
        let edge = self.prepare_loop_invariant_edge(
            loop_entry,
            iteration_entry,
            head_iterations,
            checks,
            binders,
            Some(definitions),
        )?;
        self.open_prepared_invariant_body(&edge, ranking_measures, presentation)
    }

    pub(crate) fn prepare_loop_invariant_edge(
        &self,
        loop_entry: &crate::kernel::ExecutionState,
        iteration_entry: &crate::kernel::ExecutionState,
        head_iterations: &crate::kernel::IntegerTerm,
        checks: &[crate::kernel::LoopInvariantCheck],
        binders: &[crate::kernel::LoopBinder],
        definitions: Option<&[crate::kernel::CompositeResourceDefinition]>,
    ) -> Result<PreparedLoopInvariantEdge, String> {
        let (branch, execution) = self
            .focused_frontier_execution()
            .map_err(|_| "invariant body requires an execution frontier")?;
        if execution.core.frontier.region != super::ExecutionRegionKind::LoopBody
            || !execution.core.frontier.is_at_region_boundary()
        {
            return Err("invariant body requires an unclosed loop back edge".into());
        }
        let fact_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "loop invariant bundle",
            "invariant bundle: publish effect facts",
        );
        let mut facts = branch.state.facts.clone();
        for fact in execution.core.effect_facts.iter() {
            facts = facts.with_fact(fact.proposition().clone());
        }
        for fact in crate::kernel::certified_store_equations(&execution.core.effect_facts) {
            facts = facts.with_fact(fact);
        }
        drop(fact_timing);
        let rebound_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "loop invariant bundle",
            "invariant bundle: rebind resources",
        );
        // The loop's names are bound again before any invariant reads a
        // binder field: the body may have refolded its instance under another
        // name, and the binder follows the family and arguments, not the name.
        let back_edge_state = crate::kernel::loop_state_with_loop_binders_rebound(
            iteration_entry,
            &execution.core.state,
            binders,
            facts.assumptions(),
        )
        .map_err(|error| format!("loop state join: {error}"))?;
        drop(rebound_timing);
        // D7 applied to refutation: a premise that refutes a field-free arm's
        // own fact says the folded instance's model is not that constructor.
        // A descending loop's back edge learns `left.model != Empty` from the
        // guard `root->left != 0` exactly here, which is what lets the next
        // iteration's invariant select the arm its measure and its `unfold`
        // need.
        if let Some(definitions) = definitions {
            for fact in crate::kernel::publish_instance_arms(
                back_edge_state.resources(),
                definitions,
                &back_edge_state,
                facts.assumptions(),
            )
            .model_facts
            {
                facts = facts.with_fact(fact);
            }
        }
        let lowering_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "loop invariant bundle",
            "invariant bundle: lower obligations",
        );
        let obligations = crate::kernel::loop_invariant_obligations_at_back_edge(
            &back_edge_state,
            loop_entry,
            checks,
            head_iterations,
            facts.assumptions(),
        )
        .map_err(|error| format!("loop invariant classification: {error}"))?;
        drop(lowering_timing);
        Ok(PreparedLoopInvariantEdge {
            state: back_edge_state,
            iteration_entry: iteration_entry.clone(),
            head_iterations: head_iterations.clone(),
            facts,
            obligations,
            binding: super::execution::CheckedLoopInvariantLowerings {
                retained_state: execution.core.state.clone(),
                checks: checks.to_vec(),
                ranking_measures: Vec::new(),
                facts: branch.state.facts.clone(),
                effects: execution.core.effect_facts.clone(),
                body: None,
            },
        })
    }

    /// The kernel constructs the exact root and its complete premises. The
    /// language supplies presentation only, never obligations or assumptions.
    pub(crate) fn open_prepared_invariant_body(
        &self,
        edge: &PreparedLoopInvariantEdge,
        ranking_measures: &[crate::kernel::RankingComponent],
        presentation: impl FnOnce(
            &Proposition,
            &[Option<Arc<crate::kernel::LoweringIntroductions>>],
        ) -> P,
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
        if !edge
            .binding
            .matches_context(&execution.core, &branch.state.facts)
        {
            return Err("prepared invariant edge belongs to another execution context".into());
        }
        // The ranking members follow the invariants in declaration order.
        let ranking = crate::kernel::loop_ranking_obligations_at_back_edge(
            &edge.state,
            &edge.iteration_entry,
            &edge.head_iterations,
            ranking_measures,
            edge.assumptions(),
        )
        .map_err(|reason| {
            format!("could not read the loop's declared ranking measure: {reason}")
        })?;
        let wide = edge.obligations.len() + ranking.len() > 24;
        let (members, introductions): (Vec<_>, Vec<_>) = edge
            .obligations
            .iter()
            .chain(&ranking)
            .map(|obligation| {
                let introductions = obligation.shared_introductions();
                if wide
                    && let Some(introductions) = introductions
                    && let Some((goal, adjusted)) =
                        group_wide_invariant_guards(obligation.proposition(), introductions)
                {
                    return (goal, Some(adjusted));
                }
                (obligation.proposition().clone(), introductions.cloned())
            })
            .unzip();
        // Preserve the established shape of short bundles. Wide generated
        // bundles need logarithmic conjunction depth so their explicit
        // certificates fit the unchanged source parser's structural limit.
        // Pair adjacent members only: every obligation and its order remain.
        let goal = if wide {
            balanced_invariant_conjunction(members)
        } else {
            members
                .into_iter()
                .rev()
                .reduce(|right, left| Proposition::And(Box::new(left), Box::new(right)))
        }
        .unwrap_or(Proposition::condition_is(
            crate::kernel::OldConditionTerm::Constant(true),
            true,
        ));
        let display = presentation(&goal, &introductions);
        let root = Self::root(
            self.state.locals.clone(),
            ProofBranch::new(
                ProofObligation::Proposition(super::PropositionObligation::new(goal, display)),
                ProofBranchState {
                    facts: edge.facts.clone(),
                    execution: branch.state.execution.clone(),
                },
            ),
        );
        let mut binding = edge.binding.clone();
        binding.ranking_measures = ranking_measures.to_vec();
        let scope = InvariantBodyScope {
            root: root.clone(),
            binding,
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
            .matches_context(&execution.core, &branch.state.facts)
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: requested.state.locals.clone(),
                open_branches: requested.state.open_branches.with_branch_state_at(
                    requested.focused_branch,
                    ProofBranchState {
                        facts: branch.state.facts.clone(),
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

    pub(crate) fn retain_frontier_after_case_refutation(
        &self,
        parent: &super::ExecutionProofCore,
        refuted: &Self,
    ) -> Result<Self, &'static str> {
        let (live, execution) = self
            .focused_frontier_execution()
            .map_err(|_| "the surviving case lost its frontier")?;
        let (dead, refuted_execution) = refuted
            .focused_frontier_execution()
            .map_err(|_| "the refutation lost its frontier")?;
        let mut updated = execution.clone();
        updated.core.exclude_refuted_case_sibling(
            parent,
            &refuted_execution.core,
            &dead.state.facts,
        )?;
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches: self.state.open_branches.replace_frontier_at(
                    self.focused_branch,
                    live.state.facts.clone(),
                    updated,
                ),
                added_facts: self.state.added_facts.clone(),
                checked_facts: self.state.checked_facts.clone(),
            },
            self.focused_branch,
        ))
    }

    pub(crate) fn replace_frontier_presentation(
        &self,
        presentation: S,
    ) -> Result<Self, ExecutionUpdateError> {
        let (branch, execution) = self.focused_frontier_execution()?;
        let state = ProofBranchState {
            facts: branch.state.facts.clone(),
            execution: Some(Arc::new(ProofExecutionState::new(
                execution.core.clone(),
                presentation,
            ))),
        };
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
        let ProofBranchState { facts, execution } = goal.state;
        let mut execution =
            Arc::unwrap_or_clone(execution.ok_or(ExecutionUpdateError::MissingExecution)?);
        let result = edit(&mut execution.presentation);
        state.open_branches = state.open_branches.insert_existing_at(
            focused_branch,
            ProofBranch::new(
                ProofObligation::Frontier(frontier),
                ProofBranchState {
                    facts,
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
        checks: &[crate::kernel::LoopInvariantCheck],
        ranking_measures: &[crate::kernel::RankingComponent],
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
        if !evidence
            .retained_state
            .shares_storage_with(&execution.core.state)
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
        if evidence.ranking_measures != ranking_measures {
            return Err(
                "invariant closure evidence closed a different loop ranking measure".into(),
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
            execution: Some(Arc::new(ProofExecutionState::new(
                core,
                execution.presentation.clone(),
            ))),
        };
        Ok(Self::new(
            ProofState {
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
    /// obligation. The caller remains responsible for checking
    /// the semantic transition; replacing that checked-driver boundary with
    /// typed kernel evidence would be a separate interface redesign.
    pub(crate) fn publish_checked_frontier_transition(
        &self,
        facts: PureFactStore,
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
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
    /// kernel preserves the current obligation and owns the
    /// branch identities and split topology.
    pub(crate) fn publish_checked_frontier_split(
        &self,
        arms: [(PureFactStore, ProofExecutionState<S>); 2],
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

        let [then_arm, else_arm] = arms.map(|(facts, execution)| {
            ProofBranch::new(
                ProofObligation::Frontier(frontier.clone()),
                ProofBranchState {
                    facts,
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
        arms: [Option<(PureFactStore, Arc<ProofExecutionState<S>>)>; 2],
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
                        execution: Some(execution),
                    },
                ),
            );
        }
        let deltas = introduced_facts[focused_arm].clone().unwrap_or_default();
        Ok((
            Self::new(
                ProofState {
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
        facts: PureFactStore,
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches,
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            },
            parent,
        ))
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
        if !super::execution::proof_cases_are_exhaustive(
            &branch.state.facts,
            &then_fact,
            &else_fact,
        ) {
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
            let facts = branch.state.facts.with_fact(fact.clone());
            let mut core = execution.core.clone();
            assert!(core.record_proof_case_arm(partition.clone(), arm_index, facts.clone()));
            core.retain_step_case(fact);
            ProofBranch::new(
                ProofObligation::Frontier(frontier.clone()),
                ProofBranchState {
                    facts,
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
                    termination: self.state.termination.clone(),
                    termination_root: self.state.termination_root,
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
        let facts = partition
            .facts_for_case(index)
            .ok_or("match case index is outside its partition")?;
        let additions = facts
            .introduced_since(partition.root_facts())
            .ok_or("match case facts do not extend their partition root")?;
        let mut execution = branch
            .state
            .execution
            .as_deref()
            .cloned()
            .ok_or("match requires execution state")?;
        // The arm's premises are the partition's own root facts plus its
        // canonical additions, not the branch's: the partition may carry the
        // model facts this frontier forces on the scrutinee's instance and
        // checked facts of a selected flat resource arm.
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
                termination: self.state.termination.clone(),
                termination_root: self.state.termination_root,
                locals: self.state.locals.clone(),
                open_branches: self
                    .state
                    .open_branches
                    .replace_at(self.focused_branch, successor),
                added_facts: Arc::new(additions.clone()),
                checked_facts: Arc::new(additions),
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
    /// execution state it already borrowed.
    pub(crate) fn with_facts_at(&self, at: BranchId, facts: PureFactStore) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("a fact successor requires the addressed open branch");
        };
        self.with_branch_state_at(
            at,
            ProofBranchState {
                facts,
                execution: branch.state.execution.clone(),
            },
        )
    }

    /// Retains the addressed goal under an updated execution state and
    /// facts. The successor preserves the goal's kind.
    pub(crate) fn replace_execution_at(
        &self,
        at: BranchId,
        facts: PureFactStore,
        execution: E,
    ) -> Self {
        let Some(_) = self.get(at) else {
            unreachable!("an execution successor requires the addressed open branch");
        };
        self.with_branch_state_at(
            at,
            ProofBranchState {
                facts,
                execution: Some(Arc::new(execution)),
            },
        )
    }

    /// The strict frontier successor: the addressed obligation must be an
    /// execution frontier.
    pub(crate) fn replace_frontier_at(
        &self,
        at: BranchId,
        facts: PureFactStore,
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

    pub(crate) fn is_discharged(&self) -> bool {
        self.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::PropositionObligation;
    use crate::kernel::{OldMachineTerm, Sort, Term, Variable};

    fn known_computation_proof(
        goal: Proposition,
        facts: PureFactStore,
    ) -> ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts,
                    execution: None,
                },
            ),
        )
    }

    #[test]
    fn conditional_match_identity_uses_only_its_operands() {
        use crate::instrumentation::measure_deterministic_work;
        use crate::kernel::{
            AlgebraicBitvectorMatchArm, AlgebraicTerm, AlgebraicTermNode, AlgebraicType,
            AlgebraicValue, IntegerTerm, MachineIntegerType, OldConditionTerm, ProgramValue,
            VerificationSession,
        };
        let _session = VerificationSession::enter();
        let observe = |term| IntegerTerm::from_machine(MachineIntegerType::Int32, term).unwrap();
        let guard = Variable(10);
        let zero = IntegerTerm::constant_i64(0);
        let conditional = |binder, body| {
            observe(OldMachineTerm::If {
                condition: Box::new(OldConditionTerm::integer_equal(
                    observe(OldMachineTerm::Variable(guard)),
                    zero.clone(),
                )),
                then_term: Box::new(OldMachineTerm::AlgebraicMatch {
                    scrutinee: Box::new(AlgebraicTerm {
                        algebraic_type: AlgebraicType::parameter("Payload".into()),
                        node: AlgebraicTermNode::Variable(Variable(11)),
                    }),
                    arms: vec![AlgebraicBitvectorMatchArm {
                        variant: "Item".into(),
                        bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                            OldMachineTerm::Variable(Variable(binder)),
                        ))],
                        body: OldMachineTerm::Variable(Variable(body)),
                        binding_names: Default::default(),
                    }],
                }),
                else_term: Box::new(OldMachineTerm::constant(0)),
            })
        };
        let equality = |right| {
            Proposition::condition_is(
                OldConditionTerm::integer_equal(conditional(12, 12), right),
                true,
            )
        };
        let equal = equality(conditional(13, 13));
        let different_capture = equality(conditional(13, 12));
        // Check the empty context and initialize the shared goal representation.
        assert!(
            known_computation_proof(equal.clone(), PureFactStore::default())
                .apply_known(PropositionKnownContext::Pure)
                .is_ok()
        );
        let mut baseline = None;
        // Compare populated stores, since an empty store can skip index probes.
        for size in [1, 32, 256] {
            let mut facts = PureFactStore::default();
            for n in 0..size {
                for left in [guard, Variable(1_000 + n)] {
                    facts = facts.with_fact(Proposition::condition_is(
                        OldConditionTerm::integer_less_than(
                            observe(OldMachineTerm::Variable(left)),
                            observe(OldMachineTerm::Variable(Variable(2_000 + n))),
                        ),
                        true,
                    ));
                }
            }
            let proof = known_computation_proof(equal.clone(), facts.clone());
            let (checked, work) =
                measure_deterministic_work(|| proof.apply_known(PropositionKnownContext::Pure));
            assert!(checked.is_ok());
            assert_eq!(work, *baseline.get_or_insert(work), "fact count {size}");
            assert!(
                known_computation_proof(different_capture.clone(), facts)
                    .apply_known(PropositionKnownContext::Pure)
                    .is_err()
            );
        }
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 0.7s in the parallel gate"]
    fn checked_product_bounds_use_exact_citations_as_fact_sets_grow() {
        use crate::instrumentation::measure_deterministic_work;
        use crate::kernel::{
            IntegerTerm, MachineIntegerType, OldConditionTerm, VerificationSession,
        };
        let _session = VerificationSession::enter();
        let observe = |value| {
            IntegerTerm::from_machine(MachineIntegerType::Int32, OldMachineTerm::Variable(value))
                .unwrap()
        };
        let x = Variable(10);
        let y = Variable(11);
        let goal = Proposition::condition_is(
            OldConditionTerm::integer_greater_equal(
                IntegerTerm::multiply(observe(x), observe(y)),
                IntegerTerm::constant_i64(i64::from(i32::MIN)),
            ),
            true,
        );
        let cited = super::super::arithmetic_special::positive_divisor_product_guards(&goal, false)
            .expect("signed product with positive divisor");
        let mut baseline = None;
        for size in [0, 32, 256] {
            let mut facts = PureFactStore::from_ordered(&cited);
            for n in 0..size {
                // Grow the orders mentioning x as well as the unrelated fact set.
                for lhs in [x, Variable(1_000 + n)] {
                    facts = facts.with_fact(Proposition::condition_is(
                        OldConditionTerm::integer_less_than(
                            observe(lhs),
                            observe(Variable(2_000 + n)),
                        ),
                        true,
                    ));
                }
            }
            let proof = known_computation_proof(goal.clone(), facts);
            let (checked, work) = measure_deterministic_work(|| proof.apply_close_bounds(&cited));
            assert!(checked.is_ok());
            assert_eq!(work, *baseline.get_or_insert(work), "fact count {size}");
            assert!(proof.apply_close_bounds(&cited[..1]).is_err());
        }
        let proof = known_computation_proof(goal, PureFactStore::from_ordered(&cited[..1]));
        assert!(matches!(
            proof.apply_close_bounds(&cited),
            Err(message) if message.contains("not exactly available")
        ));
    }

    #[test]
    fn known_computation_keeps_logical_introductions_explicit() {
        let truth =
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true);
        let falsehood =
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(false), true);
        for goal in [
            Proposition::Implies(Box::new(falsehood.clone()), Box::new(truth.clone())),
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                Variable(55),
                Sort::Integer,
                truth.clone(),
            ),
            crate::kernel::quantifiers::test_exists(
                Default::default(),
                Variable(55),
                Sort::Integer,
                truth.clone(),
            ),
            falsehood,
        ] {
            assert!(
                known_computation_proof(goal, PureFactStore::default())
                    .apply_known(PropositionKnownContext::Exact)
                    .is_err()
            );
        }
        for goal in [
            truth.clone(),
            Proposition::And(Box::new(truth.clone()), Box::new(truth.clone())),
            Proposition::Or(
                Box::new(Proposition::condition_is(
                    crate::kernel::OldConditionTerm::Constant(false),
                    true,
                )),
                Box::new(truth),
            ),
        ] {
            assert!(
                known_computation_proof(goal, PureFactStore::default())
                    .apply_known(PropositionKnownContext::Exact)
                    .is_ok()
            );
        }
    }

    fn integer_choice_proof(
        source: Proposition,
        facts: PureFactStore,
        goal: Proposition,
    ) -> ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> {
        assert!(facts.contains_top_level(&source));
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts,
                    execution: None,
                },
            ),
        )
    }

    fn unused_integer_existential() -> Proposition {
        crate::kernel::quantifiers::test_exists(
            "unused".into(),
            Variable(42),
            Sort::Integer,
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true),
        )
    }

    #[test]
    fn integer_choices_and_obtain_choose_witnesses() {
        let source = unused_integer_existential();
        let goal = Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true);
        let proof = integer_choice_proof(
            source.clone(),
            PureFactStore::from_ordered(std::slice::from_ref(&source)),
            goal,
        );
        for hint in [
            Variable(3_000_000),
            Variable((1 << 40) + 8),
            Variable::witness(8),
        ] {
            let (_, chosen) = proof
                .check_integer_exists_choice(&source, hint)
                .ok()
                .expect("choice");
            assert!(crate::kernel::ExecutionBudget::is_universal_witness_variable(chosen));
            let opened = proof
                .check_exists_bindings(&source, 1, hint)
                .ok()
                .expect("obtain");
            assert!(crate::kernel::ExecutionBudget::is_universal_witness_variable(opened[0].1));
        }
        let ceiling = crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_LIMIT;
        let (_, last) = proof
            .check_integer_exists_choice(&source, Variable::witness(ceiling - 1))
            .ok()
            .expect("last witness");
        assert_eq!(last, Variable::witness(ceiling - 1));
        assert!(matches!(
            proof.check_integer_exists_choice(&source, Variable::witness(ceiling)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
        assert!(matches!(
            proof.check_exists_bindings(&source, 1, Variable::witness(ceiling)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
        let exhausted = integer_choice_proof(
            source.clone(),
            PureFactStore::from_ordered(std::slice::from_ref(&source))
                .with_reserved_variables([Variable::witness(ceiling - 1)]),
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true),
        );
        assert!(matches!(
            exhausted.check_integer_exists_choice(&source, Variable(3_000_000)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
    }

    #[test]
    fn unused_universal_witness_is_reserved_before_a_choice() {
        let binder = Variable(3_200_000);
        let source = unused_integer_existential();
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source))
            .with_reserved_variables([binder]);
        let proof = integer_choice_proof(
            source.clone(),
            facts,
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                binder,
                Sort::Integer,
                Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true),
            ),
        );
        let mut introduced = None;
        let proof = proof
            .apply_intro(|_, intro, _| {
                if let PropositionIntroduction::Universal { variable, .. } = intro {
                    introduced = Some(variable);
                }
            })
            .ok()
            .expect("intro");
        let introduced = introduced.expect("universal witness");
        let (_, chosen) = proof
            .check_integer_exists_choice(&source, Variable(3_000_000))
            .ok()
            .expect("choice");
        assert_ne!(chosen, introduced);
        assert!(crate::kernel::ExecutionBudget::is_universal_witness_variable(chosen));
    }

    #[test]
    fn obtain_assigns_distinct_witnesses_to_unused_mixed_bindings() {
        let inner = unused_integer_existential();
        let source = crate::kernel::quantifiers::test_exists(
            "machine".into(),
            Variable(43),
            Sort::ProgramInt32,
            inner,
        );
        let proof = integer_choice_proof(
            source.clone(),
            PureFactStore::from_ordered(std::slice::from_ref(&source)),
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true),
        );
        let opened = proof
            .check_exists_bindings(&source, 2, Variable(3_000_000))
            .ok()
            .expect("mixed obtain");
        assert_ne!(opened[0].1, opened[1].1);
        assert!(opened.iter().all(|(_, var, _)| {
            crate::kernel::ExecutionBudget::is_universal_witness_variable(*var)
        }));
        let ceiling = crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_LIMIT;
        assert!(matches!(
            proof.check_exists_bindings(&source, 2, Variable::witness(ceiling - 1)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
    }

    #[test]
    fn integer_choice_freshens_against_focused_goal_binding() {
        let collision = Variable::witness(0);
        let source = crate::kernel::quantifiers::test_exists(
            "source".into(),
            Variable(41),
            Sort::Integer,
            Proposition::condition_is(
                crate::kernel::OldConditionTerm::IntegerEqual(
                    crate::kernel::IntegerTerm::var(Variable(41)).into(),
                    crate::kernel::IntegerTerm::var(Variable(41)).into(),
                ),
                true,
            ),
        );
        // A quantifier binds its own bound variable, so the goal mentions the
        // first witness identity free for the choice to collide with.
        let goal = Proposition::And(
            Box::new(source.clone()),
            Box::new(Proposition::condition_is(
                crate::kernel::OldConditionTerm::IntegerEqual(
                    crate::kernel::IntegerTerm::var(collision).into(),
                    crate::kernel::IntegerTerm::var(collision).into(),
                ),
                true,
            )),
        );
        type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
        let proof: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts: PureFactStore::from_ordered(std::slice::from_ref(&source)),
                    execution: None,
                },
            ),
        );
        let (_, witness) = match proof.check_integer_exists_choice(&source, collision) {
            Ok(choice) => choice,
            Err(_) => panic!("the kernel should freshen a choice colliding with the focused goal"),
        };
        assert_ne!(witness, collision);
    }

    #[test]
    fn integer_choice_freshens_against_unused_ambient_binding() {
        let ambient = Variable::witness(0);
        let source = crate::kernel::quantifiers::test_exists(
            "source".into(),
            Variable(51),
            Sort::Integer,
            Proposition::condition_is(
                crate::kernel::OldConditionTerm::IntegerEqual(
                    crate::kernel::IntegerTerm::var(Variable(51)).into(),
                    crate::kernel::IntegerTerm::var(Variable(51)).into(),
                ),
                true,
            ),
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source))
            .with_reserved_variables([ambient]);
        let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
            ProofObject::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(
                        Proposition::Predicate {
                            name: "later_ambient_reference".into(),
                            arguments: vec![],
                        },
                        (),
                    )),
                    ProofBranchState {
                        facts,
                        execution: None,
                    },
                ),
            );
        let (_, witness) = match proof.check_integer_exists_choice(&source, ambient) {
            Ok(choice) => choice,
            Err(_) => panic!("the kernel should retain ambient reservations across subgoals"),
        };
        assert_ne!(witness, ambient);
    }

    /// A universal introduction's witness stands for an arbitrary value, so
    /// it must name nothing the surrounding state already names. This used to
    /// be decided by counting up from `Variable(0)` for an identity no *fact*
    /// mentions, which is the C identity range: the witness became a live
    /// program variable of the function being proved whenever the low
    /// identities happened to be absent from the fact set, as they are for a
    /// pointer parameter. The range is the guarantee now, so the assertion is
    /// about the range and not about which identities a particular fact set
    /// happens to hold.
    #[test]
    fn a_freshened_universal_witness_never_takes_a_program_identity() {
        let bound = Variable(2_000_000);
        let body = Proposition::condition_is(
            crate::kernel::OldConditionTerm::signed_less_equal(
                OldMachineTerm::constant(0),
                OldMachineTerm::Variable(bound),
            ),
            true,
        );
        // The only fact reserves the binder, exactly as an earlier universal
        // `have` over the same lowered binder identity does. Nothing mentions
        // `Variable(0)`, which is what used to make it the first candidate.
        let reserving = crate::kernel::quantifiers::test_forall(
            Default::default(),
            bound,
            Sort::ProgramInt32,
            body.clone(),
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&reserving));
        let (witness, _) = facts
            .freshen_int32_forall_body(bound, &body)
            .expect("a witness is left for the first introduction");
        assert!(
            crate::kernel::ExecutionBudget::is_universal_witness_variable(witness),
            "{witness:?} is not a witness, so it is some other producer's identity"
        );
        assert_ne!(
            witness,
            Variable(witness.0),
            "{witness:?} can still be a C identity or an execution identity"
        );

        // A second introduction beside the first must not name it again.
        let second = facts
            .with_fact(Proposition::condition_is(
                crate::kernel::OldConditionTerm::signed_less_equal(
                    OldMachineTerm::constant(0),
                    OldMachineTerm::Variable(witness),
                ),
                true,
            ))
            .freshen_int32_forall_body(bound, &body)
            .expect("a second witness")
            .0;
        assert_ne!(
            witness, second,
            "two witnesses in one scope are one identity, so a fact about the first is a fact about the second"
        );
    }

    /// The pointer-sorted introduction takes its witness from the same range,
    /// for the same reason: `Address::symbolic(v)` over a C identity is a
    /// pointer the function already has a name for.
    #[test]
    fn a_freshened_pointer_witness_never_takes_a_program_identity() {
        let bound = Variable(2_000_000);
        let body = Proposition::Predicate {
            name: "witness_body".into(),
            arguments: vec![Term::Bitvector32(OldMachineTerm::constant(0).into())],
        };
        let reserving = crate::kernel::quantifiers::test_forall(
            Default::default(),
            bound,
            Sort::ProgramPointer(crate::kernel::ProgramType::Int32),
            body.clone(),
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&reserving));
        let (witness, _) = facts
            .freshen_pointer_forall_body(bound, crate::kernel::ProgramType::Int32, &body)
            .expect("a witness is left");
        assert!(
            crate::kernel::ExecutionBudget::is_universal_witness_variable(witness),
            "{witness:?} is not a witness"
        );
    }

    #[test]
    fn materialized_known_accepts_same_state_alpha_facts_only() {
        use crate::kernel::proof::{
            ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
        };
        use crate::kernel::{
            Address, AddressOffset, ExecutionState, IntegerRangeFoldIndex, IntegerTerm,
            MachineIntegerType, OldConditionTerm, ProgramValue, SharedIntegerRangeEndpoint,
            SymbolicMemory,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let root = |facts: PureFactStore, goal: Proposition| {
            TestProof::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                    ProofBranchState {
                        facts,
                        execution: Some(Arc::new(ProofExecutionState::new(
                            ExecutionProofCore::at_entry(
                                ExecutionState::new(),
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
            )
        };
        let before = SymbolicMemory::new().with_block("alpha", 16);
        let loadable = |memory: SymbolicMemory, variable: Variable| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                variable,
                Sort::ProgramInt32,
                Proposition::Implies(
                    Box::new(Proposition::And(
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessEqual,
                                left: Box::new(OldMachineTerm::constant(0)),
                                right: Box::new(OldMachineTerm::Variable(variable)),
                            },
                            true,
                        )),
                        Box::new(Proposition::condition_is(
                            OldConditionTerm::Compare {
                                format: MachineIntegerType::Int32,
                                relation: CompareRelation::LessEqual,
                                left: Box::new(OldMachineTerm::Variable(variable)),
                                right: Box::new(OldMachineTerm::constant(16)),
                            },
                            true,
                        )),
                    )),
                    Box::new(Proposition::MemoryLoadable {
                        point: Default::default(),
                        memory,
                        base: Address::new("alpha".into(), AddressOffset::constant(0)),
                        bytes: (OldMachineTerm::Variable(variable)).into(),
                        wide: false,
                    }),
                ),
            )
        };
        let quantified_source = loadable(before.clone(), Variable(41));
        let quantified_goal = loadable(before.clone(), Variable(42));
        assert!(
            root(
                PureFactStore::from_ordered(std::slice::from_ref(&quantified_source)),
                quantified_goal.clone(),
            )
            .apply_known(PropositionKnownContext::Materialized)
            .is_ok()
        );
        assert!(
            root(PureFactStore::default(), quantified_goal)
                .apply_known(PropositionKnownContext::Materialized)
                .is_err()
        );

        let fold = |accumulator, item| {
            IntegerTerm::range_fold(
                IntegerRangeFoldIndex::Int32 {
                    start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
                    end: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                IntegerTerm::add(
                    IntegerTerm::var(accumulator),
                    IntegerTerm::from_machine(
                        MachineIntegerType::Int32,
                        OldMachineTerm::Variable(item),
                    )
                    .unwrap(),
                ),
            )
        };
        let fold_fact = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                IntegerTerm::var(Variable(50)).into(),
                fold(Variable(51), Variable(52)).into(),
            ),
            true,
        );
        let fold_goal = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                IntegerTerm::var(Variable(50)).into(),
                fold(Variable(61), Variable(62)).into(),
            ),
            true,
        );
        assert!(
            root(
                PureFactStore::from_ordered(std::slice::from_ref(&fold_fact)),
                fold_goal.clone(),
            )
            .apply_known(PropositionKnownContext::Materialized)
            .is_ok()
        );
        assert!(
            root(PureFactStore::default(), fold_goal.clone())
                .apply_known(PropositionKnownContext::Materialized)
                .is_err()
        );

        let changed = before.clone().store(
            Address::new("alpha".into(), AddressOffset::constant(0)),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        );
        assert!(
            root(
                PureFactStore::from_ordered(&[loadable(before, Variable(70))]),
                loadable(changed, Variable(71)),
            )
            .apply_known(PropositionKnownContext::Materialized)
            .is_err()
        );
    }

    #[test]
    fn invariant_body_does_not_assume_provisional_read_safety() {
        use crate::kernel::proof::{
            ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
        };
        use crate::kernel::{
            Address, AddressOffset, ExecutionState, LoopInvariantCheck, ProgramType, ProgramValue,
            SpecExpression, SpecPoint, SpecProposition,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let load = SpecExpression::MemoryLoad {
            point: SpecPoint::Current,
            pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
                crate::kernel::Pointer::new(
                    Address::new("unallocated".into(), AddressOffset::constant(0)),
                    ProgramType::Int32Pointer,
                ),
            ))),
            value_type: ProgramType::Int32,
            exact: false,
        };
        // An explicit validity claim needs evidence even though logical
        // reflexivity at this address would hold without memory permission.
        let checks = [LoopInvariantCheck::new(
            SpecProposition::Defined(load),
            None,
            None,
        )];
        let frontier = TestProof::root(
            (),
            ProofBranch::new(
                ProofObligation::Frontier(FrontierObligation),
                ProofBranchState {
                    facts: PureFactStore::default(),
                    execution: Some(Arc::new(ProofExecutionState::new(
                        ExecutionProofCore::at_entry(
                            ExecutionState::new(),
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
            .open_invariant_body(
                &ExecutionState::new(),
                &ExecutionState::new(),
                &crate::kernel::IntegerTerm::var(crate::kernel::Variable(9_999)),
                &checks,
                &[],
                &[],
                &[],
                |_, _| (),
            )
            .unwrap();
        assert!(body.apply_known(PropositionKnownContext::Pure).is_err());
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
            .apply_known(PropositionKnownContext::Exact)
            .ok()
            .unwrap();
        assert!(frontier.retain_invariant_body(scope, &unrelated).is_err());
    }

    #[test]
    fn completed_proposition_retains_whether_it_relied_on_root_assumptions() {
        let truth =
            Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(true), true);
        for assumed in [false, true] {
            let branch = ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(truth.clone(), ())),
                ProofBranchState {
                    facts: PureFactStore::from_ordered(if assumed {
                        std::slice::from_ref(&truth)
                    } else {
                        &[]
                    }),
                    execution: None,
                },
            );
            let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
                ProofObject::root((), branch);
            let checked = proof
                .apply_known(PropositionKnownContext::Exact)
                .ok()
                .unwrap()
                .completed_proposition()
                .unwrap();
            assert_eq!(checked.is_closed(), !assumed);
            assert_eq!(checked.proposition(), &truth);
            let falsehood =
                Proposition::condition_is(crate::kernel::OldConditionTerm::Constant(false), true);
            let guarded =
                Proposition::Implies(Box::new(falsehood.clone()), Box::new(truth.clone()));
            let weakened = checked.with_implication_prefix(&guarded, 1).unwrap();
            assert_eq!(weakened.proposition(), &guarded);
            assert_eq!(weakened.is_closed(), checked.is_closed());
            assert!(
                weakened
                    .root_assumptions()
                    .shares_assumptions_with(checked.root_assumptions())
            );
            assert!(checked.with_implication_prefix(&guarded, 0).is_none());
            assert!(checked.with_implication_prefix(&guarded, 2).is_none());
            assert!(checked.with_implication_prefix(&falsehood, 0).is_none());
            let wrong_body = Proposition::Implies(Box::new(truth.clone()), Box::new(falsehood));
            assert!(checked.with_implication_prefix(&wrong_body, 1).is_none());
        }
    }

    #[test]
    fn intro_freshens_a_universal_binder_away_from_ambient_facts() {
        let binder = Variable(186);
        let body = Proposition::Predicate {
            name: "holds".to_string(),
            arguments: vec![Term::Bitvector32(OldMachineTerm::Variable(binder).into())],
        };
        let goal = crate::kernel::quantifiers::test_forall(
            Default::default(),
            binder,
            Sort::ProgramInt32,
            body.clone(),
        );
        let branch = ProofBranch::new(
            ProofObligation::Proposition(PropositionObligation::new(goal, ())),
            ProofBranchState {
                facts: PureFactStore::from_ordered(std::slice::from_ref(&body)),
                execution: None,
            },
        );
        let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
            ProofObject::root((), branch);
        let mut introduced = None;

        let next = proof
            .apply_intro(|_, introduction, _| match introduction {
                PropositionIntroduction::Universal { variable, .. } => {
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
                arguments: vec![Term::Bitvector32(
                    OldMachineTerm::Variable(introduced).into()
                )],
            }
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/object/tests.rs");
    }
}
