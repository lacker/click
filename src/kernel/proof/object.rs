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
#[cfg(test)]
use crate::kernel::CompareRelation;
use crate::kernel::primitives::first_unavailable_connective_side;
use crate::kernel::{Proposition, Sort, Variable};
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
    DoesNotNormalize,
    ConditionalNormalization(super::fact_reasoning::ConditionalNormalizationError),
    IntegerArithmeticPremiseUnavailable(usize),
    IntegerArithmetic(super::integer_arithmetic::IntegerArithmeticCheckError),
    SignedArithmeticPremiseUnavailable(usize),
    SignedArithmetic(super::signed_arithmetic::SignedArithmeticCheckError),
    SpecialArithmeticPremiseUnavailable(usize),
    SpecialArithmetic(super::arithmetic_special::SpecialArithmeticCheckError),
    ExpectedIntroduction(Proposition),
    IntegerFresheningExhausted,
    /// The reserved universal-witness range
    /// ([`crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_BASE`])
    /// holds no identity above the witnesses already in scope. The
    /// introduction refuses rather than reusing one: an identity outside that
    /// range is some other producer's, and a witness that names a live C
    /// variable is the capture this range exists to prevent.
    UniversalWitnessFresheningExhausted,
    IntegerChoiceSourceUnavailable,
    IntegerChoiceWrongSort,
    IntegerChoiceFresheningExhausted,
    /// The goal is a conjunction or disjunction, and this side of it is the
    /// first one that no fact supplies.
    UnavailableSide(Proposition),
    ExpectedFiniteUniversal,
    MissingFiniteInstance,
    /// `contradiction(fact)` found no refutation; `fact_held` says whether
    /// the fact itself was available, so the missing half can be named.
    ContradictionUnavailable {
        fact_held: bool,
    },
    ExtractUnavailable,
    /// The explicit premise at this index of the `using` list is not held.
    InstantiatePremiseUnavailable(usize, Proposition),
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

    /// Bind an execution strategy's whole-contract progress to the exact
    /// generative outcomes this ordinary proof owner just opened.
    #[cfg(test)]
    pub(crate) fn start_contract_completion(
        &self,
        owner: &crate::kernel::WholeContractProof,
        execution: &crate::kernel::CheckedFunctionExecution,
        branches: impl Iterator<Item = BranchId>,
    ) -> Option<crate::kernel::ContractProofProgress> {
        crate::kernel::ContractProofProgress::open(
            owner,
            execution,
            branches.filter_map(|id| {
                crate::instrumentation::record_deterministic_work(1);
                let branch = self.state.open_branches.get(id)?;
                match &branch.obligation {
                    ProofObligation::FunctionOutcome(outcome) => {
                        Some((outcome.path_index, outcome.data.core.identity.clone()))
                    }
                    _ => None,
                }
            }),
        )
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

    pub(crate) fn apply_known(
        &self,
        context: PropositionKnownContext,
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        let proposition = goal.proposition();
        let available = |proposition: &Proposition| {
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
        if available(proposition) || spelled_otherwise() || observed_otherwise() {
            return Ok(self.closed_focused());
        }
        if super::fact_reasoning::computes_leaf(proposition) {
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
            available(side)
                || facts.contains(side)
                || super::fact_reasoning::order_claim_forms(side)
                    .iter()
                    .any(|form| facts.contains(form))
                || super::fact_reasoning::computes_leaf(side)
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

    pub(crate) fn apply_normalize(&self) -> Result<Self, PropositionCloseError> {
        let (goal, _) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        super::fact_reasoning::normalizes_context_free_leaf(goal.proposition())
            .then(|| self.closed_focused())
            .ok_or(PropositionCloseError::DoesNotNormalize)
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
        let fresh = branch
            .state
            .facts
            .fresh_universal_witness(&excluded)
            .ok_or(PropositionCloseError::IntegerChoiceFresheningExhausted)?;
        let variable = Variable(fresh.0.max(hint.0));
        if !crate::kernel::ExecutionBudget::is_universal_witness_variable(variable) {
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
            body, *var, &witness,
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
                        var,
                        &crate::kernel::IntegerTerm::var(chosen),
                    )
                    .map_err(|_| PropositionCloseError::IntegerChoiceFresheningExhausted)?
                }
                Sort::ProgramInt32 | Sort::ProgramInt64 | Sort::ProgramInteger(_) => {
                    crate::kernel::substitute_int32_variable_in_proposition(
                        &body,
                        var,
                        crate::kernel::MachineTerm::Variable(chosen),
                    )
                }
                Sort::ProgramPointer(program_type)
                | Sort::ProgramObjectPointer(program_type, _) => {
                    let pointer =
                        if matches!(program_type, crate::kernel::ProgramType::FunctionPointer(_)) {
                            crate::kernel::Pointer::symbolic_function(chosen)
                        } else {
                            crate::kernel::Pointer::symbolic(chosen)
                        };
                    crate::kernel::substitute_pointer_variable_in_proposition(&body, var, &pointer)
                }
                Sort::Algebraic(algebraic_type) => {
                    super::super::reasoning::substitute_algebraic_variable_in_proposition(
                        &body,
                        var,
                        &crate::kernel::AlgebraicTerm {
                            algebraic_type: algebraic_type.clone(),
                            node: crate::kernel::AlgebraicTermNode::Variable(chosen),
                        },
                    )
                }
                _ => unreachable!("checked above"),
            };
            opened.push((current.clone(), chosen, sort));
            next = Variable(
                chosen
                    .0
                    .checked_add(1)
                    .ok_or(PropositionCloseError::IntegerChoiceFresheningExhausted)?,
            );
        }
        Ok(opened)
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

    pub(crate) fn apply_preserve(
        &self,
        separation: &Proposition,
        field: Option<crate::kernel::eval::typed_reads::FieldSelection>,
    ) -> Result<Self, String> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or("preserve requires a proposition goal")?;
        super::preservation::apply(separation, field, goal.proposition(), |p| facts.contains(p))?;
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
            if !facts.listed_premise_available(premise, &[], false) {
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

    pub(crate) fn apply_signed_arithmetic(
        &self,
        certificate: &super::signed_arithmetic::SignedArithmeticCertificate,
        premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        for (index, premise) in premises.iter().enumerate() {
            if !facts.listed_premise_available(premise, &[], false) {
                return Err(PropositionCloseError::SignedArithmeticPremiseUnavailable(
                    index,
                ));
            }
        }
        certificate
            .check(goal.proposition(), premises)
            .map_err(PropositionCloseError::SignedArithmetic)?;
        Ok(self.closed_focused())
    }

    pub(crate) fn apply_special_arithmetic(
        &self,
        certificate: &super::arithmetic_special::SpecialArithmeticCertificate,
        premises: &[Proposition],
    ) -> Result<Self, PropositionCloseError> {
        let (goal, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        for (index, premise) in premises.iter().enumerate() {
            if !facts.listed_premise_available(premise, &[], false) {
                return Err(PropositionCloseError::SpecialArithmeticPremiseUnavailable(
                    index,
                ));
            }
        }
        certificate
            .check(goal.proposition(), premises)
            .map_err(PropositionCloseError::SpecialArithmetic)?;
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
        self.apply_intro_opening(presentation, false)
    }

    /// `intro` on a goal. A disequality (`a != b`) is the negation of its
    /// equality, so it opens like `not (a == b)`: the equality becomes a
    /// fact and the goal `false`. `written_negation` says the author wrote
    /// the goal as `not P` though lowering spelled `P`'s negation as one
    /// comparison (`not (x < y)` as `x >= y`); the complement then opens the
    /// same way. Assuming a condition's complement and refuting it proves the
    /// condition, so either opening is sound for every condition.
    pub(crate) fn apply_intro_opening(
        &self,
        presentation: impl FnOnce(&P, PropositionIntroduction, Option<&Proposition>) -> P,
        written_negation: bool,
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
                            .freshen_pointer_forall_body(*var, *program_type, body)
                            .ok_or(PropositionCloseError::UniversalWitnessFresheningExhausted)?;
                        (variable, body, Some(*program_type), None)
                    }
                    Sort::Integer => {
                        let (variable, body) = facts
                            .freshen_integer_forall_body(*var, body)
                            .ok_or(PropositionCloseError::IntegerFresheningExhausted)?;
                        (variable, body, None, None)
                    }
                    Sort::Algebraic(algebraic_type) => {
                        let (variable, body) = facts
                            .freshen_algebraic_forall_body(*var, algebraic_type, body)
                            .ok_or(PropositionCloseError::UniversalWitnessFresheningExhausted)?;
                        (variable, body, None, Some(algebraic_type.clone()))
                    }
                    _ => {
                        let (variable, body) = facts
                            .freshen_int32_forall_body(*var, body)
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
            // A written `not forall` lowers to a defined counterexample.
            // Preserve contradiction-style introduction by assuming the exact
            // complement of that existential, including every domain conjunct.
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } if written_negation => {
                let complement = match body.as_ref() {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::ConditionIs(condition.clone(), !value)
                    }
                    Proposition::Not(inner) => inner.as_ref().clone(),
                    body => Proposition::Not(Box::new(body.clone())),
                };
                (
                    Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true),
                    Some(Proposition::ForAll {
                        name: crate::kernel::BinderName::written(name),
                        var: *var,
                        sort: sort.clone(),
                        body: Box::new(complement),
                    }),
                    PropositionIntroduction::Negation,
                )
            }
            Proposition::Not(body) => (
                Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true),
                Some(body.as_ref().clone()),
                PropositionIntroduction::Negation,
            ),
            Proposition::ConditionIs(condition, value)
                if written_negation || condition_is_disequality(condition, *value) =>
            {
                let complement = match condition {
                    crate::kernel::ConditionTerm::IntegerNotEqual(left, right) => {
                        Proposition::ConditionIs(
                            crate::kernel::ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                            *value,
                        )
                    }
                    _ => Proposition::ConditionIs(condition.clone(), !*value),
                };
                (
                    Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true),
                    Some(complement),
                    PropositionIntroduction::Negation,
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

    pub(crate) fn apply_contradiction(
        &self,
        fact: &Proposition,
    ) -> Result<Self, PropositionCloseError> {
        let branch = self
            .state
            .open_branches
            .get(self.focused_branch)
            .ok_or(PropositionCloseError::Unavailable)?;
        let facts = &branch.state.facts;
        facts
            .contradicts(fact)
            .then(|| self.closed_focused())
            .ok_or_else(|| PropositionCloseError::ContradictionUnavailable {
                fact_held: facts.holds_contradiction_fact(fact),
            })
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
        let proposition = if branch.state.facts.contains_proper_conjunct(&proposition)
            || branch
                .state
                .facts
                .contains_discharged_implication_consequent(&proposition)
            || branch
                .state
                .facts
                .assumptions()
                .contains_algebraic_constructor_field_equality(&proposition)
        {
            proposition
        } else if let Some(conjunct) = branch
            .state
            .facts
            .alpha_equivalent_proper_conjunct(&proposition)
        {
            // The cited universal under other binder names: extract the
            // conjunct itself.
            conjunct
        } else if branch
            .state
            .facts
            .contains_disjunction_projection(&proposition)
        {
            proposition
        } else {
            return Err(PropositionCloseError::ExtractUnavailable);
        };
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
        argument: super::fact_reasoning::InstanceArgument,
        explicit_premises: Option<&[Proposition]>,
    ) -> Result<Self, PropositionCloseError> {
        let (_, facts) = self
            .focused_proposition()
            .ok_or(PropositionCloseError::NotProposition)?;
        // Without a written list the premises are the instantiated guards
        // themselves: one availability lookup per guard conjunct, no search.
        let guard_premises;
        let explicit_premises = match explicit_premises {
            Some(premises) => premises,
            None => {
                guard_premises = super::fact_reasoning::instantiated_guard_conjuncts(
                    facts
                        .contains(&quantified)
                        .then_some(&quantified)
                        .or(facts.matching_quantified_fact(&quantified).as_ref())
                        .ok_or(PropositionCloseError::InstantiateQuantifiedUnavailable)?,
                    &argument,
                )
                .map_err(PropositionCloseError::InstantiateInvalid)?;
                if let Some(missing) = guard_premises
                    .iter()
                    .find(|guard| !facts.listed_premise_available(guard, &[], true))
                {
                    return Err(PropositionCloseError::InstantiateInvalid(
                        super::fact_reasoning::ForallInstantiationError::MissingGuard(
                            missing.clone(),
                        ),
                    ));
                }
                &guard_premises
            }
        };
        for (index, premise) in explicit_premises.iter().enumerate() {
            if !facts.listed_premise_available(premise, &[], true) {
                return Err(PropositionCloseError::InstantiatePremiseUnavailable(
                    index,
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
            crate::kernel::Term::Algebraic(value.clone()),
            crate::kernel::Term::Algebraic(value.clone()),
        );
        let reserved = crate::kernel::proposition_variables(goal.proposition())
            .into_iter()
            .chain(crate::kernel::proposition_variables(&equality))
            .collect();
        let first = facts
            .fresh_universal_witness(&reserved)
            .ok_or("match has exhausted fresh universal witness identities")?;
        let mut variables = crate::kernel::KernelVariableGenerator::fresh_for(first.0, reserved);
        let cases = crate::kernel::api::algebraic_constructor_case_equations(value, &mut || {
            variables.next()
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
                binders.iter().rev().fold(
                    Proposition::Implies(
                        Box::new(case.clone()),
                        Box::new(goal.proposition().clone()),
                    ),
                    |body, (var, sort)| Proposition::ForAll {
                        name: Default::default(),
                        var: *var,
                        sort: sort.clone(),
                        body: Box::new(body),
                    },
                )
            })
            .collect::<Vec<_>>();
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
        // Membership is by comparison form, so a written disjunction reading
        // stored cells finds the one over the values stored there, and each
        // written disjunct is equivalent to its stored-value form.
        if !branch.state.facts.contains(&disjunction) {
            return Err(PropositionSplitError::MissingDisjunction);
        }
        let Proposition::Or(left, right) = disjunction else {
            return Err(PropositionSplitError::ExpectedDisjunction);
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
        let (branch, execution) = self
            .focused_frontier_execution()
            .map_err(|_| "invariant body requires an execution frontier")?;
        if execution.core.frontier.region != super::ExecutionRegionKind::LoopBody
            || !execution.core.frontier.is_at_region_boundary()
            || execution.core.region_invariants_close_requested
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
        )?;
        // D7 applied to refutation: a premise that refutes a field-free arm's
        // own fact says the folded instance's model is not that constructor.
        // A descending loop's back edge learns `left.model != Empty` from the
        // guard `root->left != 0` exactly here, which is what lets the next
        // iteration's invariant select the arm its measure and its `unfold`
        // need.
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
        drop(rebound_timing);
        let lowering_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "loop invariant bundle",
            "invariant bundle: lower obligations",
        );
        let mut obligations = crate::kernel::loop_invariant_obligations_at_back_edge(
            &back_edge_state,
            loop_entry,
            checks,
            head_iterations,
            facts.assumptions(),
        )
        .map_err(|_| "could not lower explicit invariant obligations")?;
        // The ranking members follow the invariants in declaration order, so
        // the bundle a retained certificate closed is the same list at every
        // site that rechecks it.
        obligations.extend(
            crate::kernel::loop_ranking_obligations_at_back_edge(
                &back_edge_state,
                iteration_entry,
                head_iterations,
                ranking_measures,
                facts.assumptions(),
            )
            .map_err(|reason| {
                format!("could not read the loop's declared ranking measure: {reason}")
            })?,
        );
        drop(lowering_timing);
        let mut members: Vec<_> = obligations
            .iter()
            .map(|obligation| obligation.proposition().clone())
            .collect();
        // Preserve the established shape of short bundles. Wide generated
        // bundles need logarithmic conjunction depth so their explicit
        // certificates fit the unchanged source parser's structural limit.
        // Pair adjacent members only: every obligation and its order remain.
        let goal = if members.len() <= 24 {
            members
                .into_iter()
                .rev()
                .reduce(|right, left| Proposition::And(Box::new(left), Box::new(right)))
        } else {
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
        .unwrap_or(Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(true),
            true,
        ));
        let introductions = obligations
            .iter()
            .map(|obligation| obligation.shared_introductions().cloned())
            .collect::<Vec<_>>();
        let display = presentation(&goal, &introductions);
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
                retained_state: execution.core.state.clone(),
                checks: checks.to_vec(),
                ranking_measures: ranking_measures.to_vec(),
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
            .retained_state
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

    /// Retains the addressed goal under an updated execution state and
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

/// Whether `condition` at `value` states that two values differ: an equality
/// at `false`, or an `Integer` disequality at `true`.
fn condition_is_disequality(condition: &crate::kernel::ConditionTerm, value: bool) -> bool {
    use crate::kernel::ConditionTerm::*;
    match condition {
        IntegerNotEqual(..) => value,
        Compare {
            relation: crate::kernel::CompareRelation::Equal,
            ..
        }
        | IntegerEqual(..)
        | AlgebraicEqual(..)
        | PointerEqual(..)
        | PointerValueEqual(..)
        | PointerOffsetEqual(..) => !value,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::PropositionObligation;
    use crate::kernel::{MachineTerm, Sort, Term, Variable};

    fn known_computation_proof(
        goal: Proposition,
        facts: ProofFacts,
    ) -> ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> {
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        )
    }

    #[test]
    fn known_computation_keeps_logical_introductions_explicit() {
        let truth = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true);
        let falsehood =
            Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
        for goal in [
            Proposition::Implies(Box::new(falsehood.clone()), Box::new(truth.clone())),
            Proposition::ForAll {
                name: Default::default(),
                var: Variable(55),
                sort: Sort::Integer,
                body: Box::new(truth.clone()),
            },
            Proposition::Exists {
                name: Default::default(),
                var: Variable(55),
                sort: Sort::Integer,
                body: Box::new(truth.clone()),
            },
            falsehood,
        ] {
            assert!(
                known_computation_proof(goal, ProofFacts::default())
                    .apply_known(PropositionKnownContext::Exact)
                    .is_err()
            );
        }
        for goal in [
            truth.clone(),
            Proposition::And(Box::new(truth.clone()), Box::new(truth.clone())),
            Proposition::Or(
                Box::new(Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::Constant(false),
                    true,
                )),
                Box::new(truth),
            ),
        ] {
            assert!(
                known_computation_proof(goal, ProofFacts::default())
                    .apply_known(PropositionKnownContext::Exact)
                    .is_ok()
            );
        }
    }

    fn integer_choice_proof(
        source: Proposition,
        facts: ProofFacts,
        goal: Proposition,
    ) -> ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> {
        assert!(facts.contains_top_level(&source));
        ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts,
                    unfolded_predicates: PersistentOrderedSet::default(),
                    execution: None,
                },
            ),
        )
    }

    fn unused_integer_existential() -> Proposition {
        Proposition::Exists {
            name: "unused".into(),
            var: Variable(42),
            sort: Sort::Integer,
            body: Box::new(Proposition::ConditionIs(
                crate::kernel::ConditionTerm::Constant(true),
                true,
            )),
        }
    }

    #[test]
    fn integer_choices_and_obtain_stay_in_the_witness_band() {
        let source = unused_integer_existential();
        let goal = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true);
        let proof = integer_choice_proof(
            source.clone(),
            ProofFacts::from_ordered(std::slice::from_ref(&source)),
            goal,
        );
        for hint in [Variable(3_000_000), Variable((1 << 40) + 8)] {
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
        let ceiling = crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_CEILING;
        let (_, last) = proof
            .check_integer_exists_choice(&source, Variable(ceiling - 1))
            .ok()
            .expect("last witness");
        assert_eq!(last, Variable(ceiling - 1));
        assert!(matches!(
            proof.check_integer_exists_choice(&source, Variable(ceiling)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
        assert!(matches!(
            proof.check_exists_bindings(&source, 1, Variable(ceiling)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
        let exhausted = integer_choice_proof(
            source.clone(),
            ProofFacts::from_ordered(std::slice::from_ref(&source))
                .with_reserved_variables([Variable(ceiling - 1)]),
            Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
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
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source))
            .with_reserved_variables([binder]);
        let proof = integer_choice_proof(
            source.clone(),
            facts,
            Proposition::ForAll {
                name: Default::default(),
                var: binder,
                sort: Sort::Integer,
                body: Box::new(Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::Constant(true),
                    true,
                )),
            },
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
        let source = Proposition::Exists {
            name: "machine".into(),
            var: Variable(43),
            sort: Sort::ProgramInt32,
            body: Box::new(inner),
        };
        let proof = integer_choice_proof(
            source.clone(),
            ProofFacts::from_ordered(std::slice::from_ref(&source)),
            Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true),
        );
        let opened = proof
            .check_exists_bindings(&source, 2, Variable(3_000_000))
            .ok()
            .expect("mixed obtain");
        assert_ne!(opened[0].1, opened[1].1);
        assert!(opened.iter().all(|(_, var, _)| {
            crate::kernel::ExecutionBudget::is_universal_witness_variable(*var)
        }));
        let ceiling = crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_CEILING;
        assert!(matches!(
            proof.check_exists_bindings(&source, 2, Variable(ceiling - 1)),
            Err(PropositionCloseError::IntegerChoiceFresheningExhausted)
        ));
    }

    #[test]
    fn integer_choice_freshens_against_focused_goal_binding() {
        let collision = Variable(crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_BASE);
        let source = Proposition::Exists {
            name: "source".into(),
            var: Variable(41),
            sort: Sort::Integer,
            body: Box::new(Proposition::ConditionIs(
                crate::kernel::ConditionTerm::IntegerEqual(
                    crate::kernel::IntegerTerm::var(Variable(41)).into(),
                    crate::kernel::IntegerTerm::var(Variable(41)).into(),
                ),
                true,
            )),
        };
        let goal = Proposition::ForAll {
            name: Default::default(),
            var: collision,
            sort: Sort::Integer,
            body: Box::new(source.clone()),
        };
        type TestProof = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
        let proof: TestProof = ProofObject::root(
            (),
            ProofBranch::new(
                ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                ProofBranchState {
                    facts: ProofFacts::from_ordered(std::slice::from_ref(&source)),
                    unfolded_predicates: PersistentOrderedSet::default(),
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
        let ambient = Variable(crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_BASE);
        let source = Proposition::Exists {
            name: "source".into(),
            var: Variable(51),
            sort: Sort::Integer,
            body: Box::new(Proposition::ConditionIs(
                crate::kernel::ConditionTerm::IntegerEqual(
                    crate::kernel::IntegerTerm::var(Variable(51)).into(),
                    crate::kernel::IntegerTerm::var(Variable(51)).into(),
                ),
                true,
            )),
        };
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source))
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
                        unfolded_predicates: PersistentOrderedSet::default(),
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
        let body = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::signed_less_equal(
                MachineTerm::constant(0),
                MachineTerm::Variable(bound),
            ),
            true,
        );
        // The only fact reserves the binder, exactly as an earlier universal
        // `have` over the same lowered binder identity does. Nothing mentions
        // `Variable(0)`, which is what used to make it the first candidate.
        let reserving = Proposition::ForAll {
            name: Default::default(),
            var: bound,
            sort: Sort::ProgramInt32,
            body: Box::new(body.clone()),
        };
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&reserving));
        let (witness, _) = facts
            .freshen_int32_forall_body(bound, &body)
            .expect("the witness range holds an identity for the first introduction");
        assert!(
            crate::kernel::ExecutionBudget::is_universal_witness_variable(witness),
            "{witness:?} is outside the reserved universal-witness range, so it is some other producer's identity"
        );
        assert!(
            witness.0 >= crate::kernel::ExecutionBudget::KERNEL_VARIABLE_CEILING,
            "{witness:?} can still be a C identity or an execution identity"
        );

        // A second introduction beside the first must not name it again.
        let second = facts
            .with_fact(Proposition::ConditionIs(
                crate::kernel::ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::Variable(witness),
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
    /// for the same reason: `Pointer::symbolic(v)` over a C identity is a
    /// pointer the function already has a name for.
    #[test]
    fn a_freshened_pointer_witness_never_takes_a_program_identity() {
        let bound = Variable(2_000_000);
        let body = Proposition::Predicate {
            name: "witness_body".into(),
            arguments: vec![Term::Bitvector32(MachineTerm::constant(0))],
        };
        let reserving = Proposition::ForAll {
            name: Default::default(),
            var: bound,
            sort: Sort::ProgramPointer(crate::kernel::ProgramType::Int32),
            body: Box::new(body.clone()),
        };
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&reserving));
        let (witness, _) = facts
            .freshen_pointer_forall_body(bound, crate::kernel::ProgramType::Int32, &body)
            .expect("the witness range holds an identity");
        assert!(
            crate::kernel::ExecutionBudget::is_universal_witness_variable(witness),
            "{witness:?} is outside the reserved universal-witness range"
        );
    }

    #[test]
    fn materialized_known_accepts_same_state_alpha_facts_only() {
        use crate::kernel::proof::{
            ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition,
        };
        use crate::kernel::{
            ConditionTerm, ExecutionState, IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType,
            Memory, Pointer, PointerOffsetTerm, ProgramValue, SharedIntegerRangeEndpoint,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let root = |facts: ProofFacts, goal: Proposition| {
            TestProof::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                    ProofBranchState {
                        facts,
                        unfolded_predicates: PersistentOrderedSet::default(),
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
        let before = Memory::new().with_block("alpha", 16);
        let loadable = |memory: Memory, variable| Proposition::ForAll {
            name: Default::default(),
            var: variable,
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::Implies(
                Box::new(Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessEqual,
                            left: Box::new(MachineTerm::constant(0)),
                            right: Box::new(MachineTerm::Variable(variable)),
                        },
                        true,
                    )),
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessEqual,
                            left: Box::new(MachineTerm::Variable(variable)),
                            right: Box::new(MachineTerm::constant(16)),
                        },
                        true,
                    )),
                )),
                Box::new(Proposition::MemoryLoadable {
                    memory,
                    base: Pointer {
                        block: "alpha".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    bytes: MachineTerm::Variable(variable),
                    wide: false,
                }),
            )),
        };
        let quantified_source = loadable(before.clone(), Variable(41));
        let quantified_goal = loadable(before.clone(), Variable(42));
        assert!(
            root(
                ProofFacts::from_ordered(std::slice::from_ref(&quantified_source)),
                quantified_goal.clone(),
            )
            .apply_known(PropositionKnownContext::Materialized)
            .is_ok()
        );
        assert!(
            root(ProofFacts::default(), quantified_goal)
                .apply_known(PropositionKnownContext::Materialized)
                .is_err()
        );

        let fold = |accumulator, item| {
            IntegerTerm::range_fold(
                IntegerRangeFoldIndex::Int32 {
                    start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
                    end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(2)),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                IntegerTerm::add(
                    IntegerTerm::var(accumulator),
                    IntegerTerm::from_machine(
                        MachineIntegerType::Int32,
                        MachineTerm::Variable(item),
                    )
                    .unwrap(),
                ),
            )
        };
        let fold_fact = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::var(Variable(50)).into(),
                fold(Variable(51), Variable(52)).into(),
            ),
            true,
        );
        let fold_goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::var(Variable(50)).into(),
                fold(Variable(61), Variable(62)).into(),
            ),
            true,
        );
        assert!(
            root(
                ProofFacts::from_ordered(std::slice::from_ref(&fold_fact)),
                fold_goal.clone(),
            )
            .apply_known(PropositionKnownContext::Materialized)
            .is_ok()
        );
        assert!(
            root(ProofFacts::default(), fold_goal.clone())
                .apply_known(PropositionKnownContext::Materialized)
                .is_err()
        );

        let changed = before.clone().store(
            Pointer {
                block: "alpha".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramValue::Int32(MachineTerm::constant(7)),
        );
        assert!(
            root(
                ProofFacts::from_ordered(&[loadable(before, Variable(70))]),
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
            ExecutionState, LoopInvariantCheck, Pointer, PointerOffsetTerm, ProgramType,
            ProgramValue, SpecExpression, SpecMemory, SpecProposition,
        };
        type TestProof = ProofObject<
            (),
            ProofObligation<(), Arc<OutcomeProofState<()>>>,
            ProofExecutionState<()>,
        >;
        let load = SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::Value(ProgramValue::Pointer(
                crate::kernel::PointerValue::new(
                    Pointer {
                        block: "unallocated".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    ProgramType::Int32Pointer,
                ),
            ))),
            value_type: ProgramType::Int32,
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
                    facts: ProofFacts::default(),
                    unfolded_predicates: PersistentOrderedSet::default(),
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
        assert!(body.apply_normalize().is_err());
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
            let falsehood =
                Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true);
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
    fn negated_universal_intro_keeps_the_counterexample_domain() {
        let variable = Variable(186);
        let domain = Proposition::Predicate {
            name: "defined".into(),
            arguments: vec![Term::Bitvector32(MachineTerm::Variable(variable))],
        };
        let truth = Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(true), true);
        let body = Proposition::And(Box::new(domain), Box::new(truth));
        let goal = Proposition::Exists {
            name: "x".into(),
            var: variable,
            sort: Sort::ProgramInt32,
            body: Box::new(body.clone()),
        };
        let proof: ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()> =
            ProofObject::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(goal, ())),
                    ProofBranchState {
                        facts: ProofFacts::from_ordered(&[]),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: None,
                    },
                ),
            );
        assert!(proof.apply_intro(|_, _, _| ()).is_err());
        let next = proof
            .apply_intro_opening(
                |_, introduction, introduced| {
                    assert!(matches!(introduction, PropositionIntroduction::Negation));
                    assert_eq!(
                        introduced,
                        Some(&Proposition::ForAll {
                            name: crate::kernel::BinderName::written("x"),
                            var: variable,
                            sort: Sort::ProgramInt32,
                            body: Box::new(Proposition::Not(Box::new(body.clone()))),
                        })
                    );
                },
                true,
            )
            .unwrap_or_else(|_| panic!("written negation opens by contradiction"));
        assert_eq!(
            next.focused_proposition().unwrap().0.proposition(),
            &Proposition::ConditionIs(crate::kernel::ConditionTerm::Constant(false), true)
        );
        assert!(next.apply_normalize().is_err());
    }

    #[test]
    fn intro_freshens_a_universal_binder_away_from_ambient_facts() {
        let binder = Variable(186);
        let body = Proposition::Predicate {
            name: "holds".to_string(),
            arguments: vec![Term::Bitvector32(MachineTerm::Variable(binder))],
        };
        let goal = Proposition::ForAll {
            name: Default::default(),
            var: binder,
            sort: Sort::ProgramInt32,
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
                arguments: vec![Term::Bitvector32(MachineTerm::Variable(introduced))],
            }
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/object/tests.rs");
    }
}
