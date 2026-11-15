use super::pure_theorems::{
    PureInductionSetup, PureStructuralInductionBranchSetup, PureTheoremContext,
};
use super::*;
use crate::kernel::FunctionExecutionCandidate;
use crate::kernel::proof::{
    BranchId, CheckedBranchSplit, CheckedCallOutcomeSplit, ClaimGoalError, ClaimGoalEvidence,
    ExecutionUpdateError, FrontierObligation, FrontierSplitError, FunctionOutcomeObligation,
    OutcomeClaimGoals, OutcomeProofCore, OutcomeProofState as KernelOutcomeProofState, ProofBranch,
    ProofBranchState, ProofExecutionState as KernelProofExecutionState, ProofFacts,
    ProofFocusError, ProofJoinError, ProofObject as KernelProofObject,
    ProofObligation as KernelBranchObligation, ProofState as KernelProofState,
    PropositionCloseError, PropositionIntroduction, PropositionKnownContext,
    PropositionObligation as KernelPropositionObligation, PropositionSplitError, SplitId,
};
use crate::persistent::PersistentMap;

#[cfg(test)]
use crate::persistent::persistent_node_allocations;

use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static CHECKED_EXECUTION_INTERFACE_JOINS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static CHECKED_EXPANDED_EXECUTION_IFS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static FINALIZATION_VIEW_CONSTRUCTIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static CHOSEN_PROJECTION_WALK_WORK: std::cell::Cell<(usize, usize)> = const {
        std::cell::Cell::new((0, 0))
    };
    static TERMINAL_PUBLICATION_VISITS: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
    static TERMINAL_JOIN_MATERIALIZED_FACTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static CHECKED_HAVE_OPERATIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn take_checked_have_operations() -> usize {
    CHECKED_HAVE_OPERATIONS.with(|count| count.replace(0))
}

#[cfg(test)]
pub(in crate::surface) fn count_checked_execution_interface_joins<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = CHECKED_EXECUTION_INTERFACE_JOINS.with(std::cell::Cell::get);
    let result = operation();
    let after = CHECKED_EXECUTION_INTERFACE_JOINS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::surface) fn count_finalization_view_constructions<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = FINALIZATION_VIEW_CONSTRUCTIONS.with(std::cell::Cell::get);
    let result = operation();
    let after = FINALIZATION_VIEW_CONSTRUCTIONS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::surface) fn count_checked_expanded_execution_ifs<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = CHECKED_EXPANDED_EXECUTION_IFS.with(std::cell::Cell::get);
    let result = operation();
    let after = CHECKED_EXPANDED_EXECUTION_IFS.with(std::cell::Cell::get);
    (result, after - before)
}

/// Immutable checked proof state exposed to smart tactics.
///
/// Cloning a `Proof` shares its semantic state and derivation prefix. Applying
/// a step copies only persistent index paths and the step's own semantic delta;
/// proposition, fixed-state, and execution-frontier goals use the same boundary.
#[derive(Clone)]
pub(super) struct Proof<'a> {
    pub(in crate::surface::proof) context: Arc<ProofContext<'a>>,
    state: KernelProofHandle,
    node: Arc<ProofNode>,
    /// Diagnostic addressing for the step being checked: which source tactic,
    /// and inside which `have`/`open` blocks. This never affects checking.
    site: ProofStepSite,
}

/// Feasible arms of one checked C `if` frontier.
///
/// Entering the container performs the audited condition transition and C
/// frontier movement once. Arm bodies then extend the retained `Proof`
/// descendants; a join owns the corresponding structured certificate node.
/// Bookkeeping for one in-`Proof` execution branch split: the split
/// identity and marker its joins verify, each feasible arm's recorded goal
/// id, condition theorem, and split-time fact base (the ancestor for
/// `introduced_since`), and the shared continuation data. This is a record
/// the audited joins check — never semantic authority.
pub(super) type ExecutionSplit<'a> = Arc<ExecutionSplitData<'a>>;

/// Immutable split output. Keeping the captured states behind one handle
/// prevents every nested execution driver from reserving them on its stack.
pub(super) struct ExecutionSplitData<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    arm_branches: [Option<BranchId>; 2],
    condition_theorems: [Option<Theorem>; 2],
    checked_split: CheckedExecutionSplit,
    base_facts: [Option<ProofFacts>; 2],
    base_executions: [Option<Arc<ExecutionProofState>>; 2],
    path_facts: [Option<Vec<Proposition>>; 2],
    parent_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    statement_index: usize,
    continuation_index: usize,
    continuation_remaining: Option<Arc<ProgramStatement>>,
    execution_start_state: ExecutionState,
    /// The exact statement/state used when this split was certified.  C
    /// branch splits can recover these from the parent frontier; a throwing
    /// call may first descend through a transparent try body, so it cannot.
    split_state: ExecutionState,
    split_statement: ProgramStatement,
}

#[derive(Clone)]
pub(super) enum CheckedExecutionSplit {
    Branch(CheckedBranchSplit),
    CallOutcomes(CheckedCallOutcomeSplit),
}

/// What a proof-level case split splits on, as written. A proof `if P`
/// gives its arms `P` and `not P`; `cases` gives them the two sides of an
/// available disjunction, nested on the left for more than two arms as
/// `A or B or C` parses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::surface::proof) enum ProofCaseCondition {
    If(ClickProposition),
    Cases(ClickProposition),
}

impl ProofCaseCondition {
    /// The written proposition: the `if` condition, or the `cases`
    /// disjunction. It names the split in recorded routes.
    pub(in crate::surface::proof) fn proposition(&self) -> &ClickProposition {
        match self {
            Self::If(condition) | Self::Cases(condition) => condition,
        }
    }

    pub(in crate::surface::proof) fn is_cases(&self) -> bool {
        matches!(self, Self::Cases(_))
    }

    /// The certificate step for the split with its two arm proofs.
    pub(in crate::surface::proof) fn step(
        &self,
        ensuring: Option<Vec<ProofAssertion>>,
        then_proof: ProofCertificate,
        else_proof: ProofCertificate,
    ) -> ProofStep {
        match self {
            Self::If(condition) => ProofStep::If {
                condition: condition.clone(),
                ensuring,
                then_proof: Box::new(then_proof),
                else_proof: Box::new(else_proof),
            },
            Self::Cases(disjunction) => {
                debug_assert!(ensuring.is_none(), "`cases` has no join interface");
                ProofStep::Cases {
                    disjunction: disjunction.clone(),
                    left_proof: Box::new(then_proof),
                    right_proof: Box::new(else_proof),
                }
            }
        }
    }

    /// The written tactic for the split with its two arms' tactics.
    pub(in crate::surface::proof) fn tactic(
        &self,
        then_tactics: Vec<ProofTactic>,
        else_tactics: Vec<ProofTactic>,
    ) -> ProofTactic {
        match self {
            Self::If(condition) => ProofTactic::If(crate::surface::ProofIf {
                condition: condition.clone(),
                ensuring: None,
                then_tactics,
                else_tactics,
            }),
            Self::Cases(disjunction) => ProofTactic::Cases(
                crate::surface::ProofCases::from_binary(disjunction, then_tactics, else_tactics),
            ),
        }
    }
}

/// Bookkeeping for an exhaustive proof-level case split over one execution
/// frontier. The split is logical rather than a C branch.
pub(super) type ExecutionProofCaseSplit<'a> = Box<ExecutionProofCaseSplitData<'a>>;

/// A logical case owns its immutable captured state once. Recursive drivers
/// retain only its handle, just as they do for a checked C split.
pub(super) struct ExecutionProofCaseSplitData<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    arm_branches: [BranchId; 2],
    case_condition: ProofCaseCondition,
    base_facts: [ProofFacts; 2],
    base_executions: [Arc<ExecutionProofState>; 2],
    path_facts: [Vec<Proposition>; 2],
    common_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    execution_start_state: ExecutionState,
    /// The lexical scope at the split. Each arm starts in it: a `match` arm
    /// that reached function exit inside one arm keeps its binders on that
    /// finished path only.
    parent_locals: ProofLocals,
}

impl ExecutionProofCaseSplitData<'_> {
    /// Whether this split is a `cases` rather than a proof `if`.
    pub(in crate::surface::proof) fn is_cases(&self) -> bool {
        self.case_condition.is_cases()
    }
}

/// One checked branch arm's contribution to a checked execution join: the
/// arm's structured certificate, final facts and execution state,
/// recorded condition theorem, and the introduction deltas the merge
/// re-applies on the shared continuation. The container join and the
/// in-`Proof` sibling join both reduce their arms to this view, so the
/// merge law has one implementation.
struct CheckedExecutionJoinArm<'v> {
    branch_id: BranchId,
    certificate: ProofCertificate,
    facts: &'v ProofFacts,
    execution: &'v ExecutionProofState,
    condition_theorem: Option<&'v Theorem>,
    introduced_facts: Vec<Proposition>,
    /// The split's effects, which the arm's own extend.
    effect_base: &'v crate::kernel::ExecutionFacts,
    /// What the arm appended to `effect_base`, taken when first read.
    introduced_effect_facts: std::cell::OnceCell<crate::kernel::ExecutionFacts>,
    introduced_derivations: Vec<Theorem>,
    introduced_unfolds: Vec<String>,
    /// Frontier-local loops the arm proved inside its region. They are
    /// checked function-proof state, so a join carries them like unfolds.
    introduced_loop_clauses: Vec<StructuralClause>,
    introduced_loop_rules: Vec<VerifiedLoopRule>,
}

#[cfg(test)]
thread_local! {
    static JOIN_ARM_EFFECT_FACTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many effects joins have taken from their arms' suffixes on this
/// thread.
#[cfg(test)]
pub(in crate::surface) fn join_arm_effect_facts() -> usize {
    JOIN_ARM_EFFECT_FACTS.with(std::cell::Cell::get)
}

impl CheckedExecutionJoinArm<'_> {
    /// The effects the arm appended after the split.
    fn introduced_effect_facts(&self) -> &crate::kernel::ExecutionFacts {
        self.introduced_effect_facts.get_or_init(|| {
            let suffix = self
                .execution
                .core
                .effect_facts
                .appended_since(self.effect_base)
                .expect("the arm's effects extend the split's");
            #[cfg(test)]
            JOIN_ARM_EFFECT_FACTS.with(|count| count.set(count.get() + suffix.len()));
            suffix
        })
    }

    /// How many effects the arm appended after the split, without taking them.
    fn introduced_effect_count(&self) -> usize {
        self.execution.core.effect_facts.len() - self.effect_base.len()
    }
}

/// The merged continuation a checked execution join produces: the shared
/// frontier context, the facts both arms established, and the structured
/// `Branch` step. Callers assemble the successor proof around it.
struct CheckedExecutionJoinParts {
    execution: ExecutionProofState,
    facts: ProofFacts,
    common_added_facts: Vec<Proposition>,
    unfolded_predicates: PersistentOrderedSet<String>,
    step: ProofStep,
    /// A terminal join's outcome paths per arm, counted only while tracing.
    trace_arm_paths: Option<[usize; 2]>,
}

impl<'a> ExecutionSplitData<'a> {
    /// `Some(take_then)` when the kernel certified exactly one feasible arm.
    pub(super) fn sole_feasible_arm(&self) -> Option<bool> {
        match self.arm_branches {
            [Some(_), None] => Some(true),
            [None, Some(_)] => Some(false),
            _ => None,
        }
    }

    /// The recorded sibling goal id for one arm, when that arm is feasible.
    pub(super) fn arm_id(&self, take_then: bool) -> Option<BranchId> {
        self.arm_branches[usize::from(!take_then)]
    }

    /// The structural preflight for `branch ensuring` on this split: a
    /// decided path always supports an interface, and a two-arm join does
    /// when the shared continuation is derivable and both arm states
    /// descend from the parent's resource context.
    pub(super) fn supports_interface_branch(&self) -> bool {
        // A branch that ends a bounded region has no derivable continuation:
        // its join rests the parent at its own typed boundary instead.
        let continuation_reachable = derive_execution_join_continuation(
            &self.parent_execution,
            &self.continuation_remaining,
            self.continuation_index,
        )
        .is_some()
            || !matches!(
                self.parent_execution.core.frontier.region,
                ExecutionRegionKind::Function
            );
        self.sole_feasible_arm().is_some()
            || (continuation_reachable
                && self.base_executions.iter().flatten().all(|execution| {
                    execution
                        .core
                        .state
                        .resources()
                        .descends_from(self.parent_execution.core.state.resources())
                }))
    }
}

/// The audited branch-entry result shared by the execution container and
/// the in-`Proof` sibling split: source structure plus each feasible arm's
/// checked facts, state, path-fact delta, and condition theorem.
struct PreparedExecutionBranch {
    statement_index: usize,
    continuation_index: usize,
    continuation_remaining: Option<Arc<ProgramStatement>>,
    execution_start_state: ExecutionState,
    checked_condition_split: CheckedBranchSplit,
    arms: [Option<PreparedExecutionArm>; 2],
}

struct PreparedExecutionArm {
    facts: ProofFacts,
    execution: ExecutionProofState,
    path_facts: Vec<Proposition>,
    condition_theorem: Theorem,
}

/// The exact nonterminal frontier reached after a checked C branch completes.
///
/// A branch at the end of an enclosing arm has no direct `remaining`
/// statement. In that case execution resumes by popping the already-owned
/// persistent continuation stack. Deriving that structural result from the
/// root lets both descendants be checked against one independently computed
/// frontier rather than selecting either arm's execution state.
#[derive(Clone)]
struct ExecutionBranchJoinContinuation {
    remaining: Arc<ProgramStatement>,
    next_statement_index: usize,
    continuations: PersistentSequence<ProofExecutionContinuation>,
}

/// Derives the exact nonterminal frontier reached after a checked C branch
/// completes, from the branch root's execution and recorded continuation
/// data. See [`ExecutionBranchJoinContinuation`].
fn derive_execution_join_continuation(
    root_execution: &ExecutionProofState,
    continuation_remaining: &Option<Arc<ProgramStatement>>,
    continuation_index: usize,
) -> Option<ExecutionBranchJoinContinuation> {
    let mut continuations = root_execution.core.frontier.continuations.clone();
    if let Some(remaining) = continuation_remaining {
        return Some(ExecutionBranchJoinContinuation {
            remaining: remaining.clone(),
            next_statement_index: continuation_index,
            continuations,
        });
    }

    while let Some(continuation) = continuations.pop() {
        if let Some(remaining) = continuation.remaining {
            return Some(ExecutionBranchJoinContinuation {
                remaining,
                next_statement_index: continuation.next_statement_index,
                continuations,
            });
        }
    }
    None
}

/// One nested proposition proof owned by an audited scope operation.
#[derive(Clone)]
pub(super) struct ProofScope<'a> {
    root: Proof<'a>,
    structure: Box<ProofScopeStructure>,
    body: Proof<'a>,
    introduced_facts: Vec<Proposition>,
    /// The selected producer judgment and its consumed implication prefix.
    /// Shared metadata; source-step descendants never copy the original goal.
    loop_entry_goal: Option<(Arc<crate::kernel::ProofObligation>, usize)>,
}

#[derive(Clone)]
enum ProofScopeStructure {
    Have {
        proposition: ClickProposition,
        kernel: Proposition,
        /// The initial unfolded goal, published only after the body closes.
        retained_body: Option<(ClickProposition, Proposition)>,
    },
    Open {
        resource: ResourceClause,
        source_index: usize,
        preserve_exposed_body: bool,
        /// The source's `open(r) { ... } by { ... }` proof of the body fact
        /// the closing fold leaves open.
        written_close_proof: Option<Vec<ProofTactic>>,
    },
}

type ProofState = KernelProofState<ProofLocals, Obligation, ExecutionProofState>;

struct CheckedFocusedTransition {
    locals: ProofLocals,
    branch: Option<OpenBranch>,
    added_facts: Vec<Proposition>,
    checked_facts: Vec<Proposition>,
}

impl CheckedFocusedTransition {
    fn replacing(
        locals: ProofLocals,
        branch: Option<OpenBranch>,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> Self {
        Self {
            locals,
            branch,
            added_facts,
            checked_facts,
        }
    }

    fn clear_chosen_projection(&mut self) {
        if let Some(branch) = self.branch.as_mut()
            && let Some(execution) = branch.state.execution.as_deref()
        {
            let mut execution = execution.clone();
            execution.presentation.chosen_projection = None;
            execution.presentation.existential_projection = None;
            branch.state.execution = Some(Arc::new(execution));
        }
    }
}

/// Proof-local surface names introduced by checked refinements such as
/// `choose`. The persistent map makes forks and one local binding logarithmic;
/// the counter is branch-local scalar freshness state.
#[derive(Clone)]
struct ProofLocals {
    values: PersistentMap<String, ContractExpression>,
    value_names: binding_names::BindingNames,
    integer_values: PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    algebraic_values: PersistentMap<String, crate::kernel::SpecAlgebraicExpression>,
    /// Authored spellings used for premise lookup and certificate printing.
    /// A recorded form is an index, not authority; lookups still validate it.
    surface_facts: SurfacePropositionMap,
    /// Normalized spellings of checked fixed-state/outcome conclusions.
    /// These can contain captured values with no printable source form, so
    /// they serve explicit fact lookup only, never certificate source choice.
    checked_lowerings: SurfacePropositionMap,
    next_choice_variable: u64,
}

pub(in crate::surface::proof) mod binding_names;

impl ProofLocals {
    fn set_values(&mut self, values: PersistentMap<String, ContractExpression>) {
        self.value_names.update_values(&self.values, &values);
        self.values = values;
    }

    fn set_integer_values(
        &mut self,
        values: PersistentMap<String, crate::kernel::SpecIntegerExpression>,
    ) {
        self.value_names
            .update_integers(&self.integer_values, &values);
        self.integer_values = values;
    }

    fn set_algebraic_values(
        &mut self,
        values: PersistentMap<String, crate::kernel::SpecAlgebraicExpression>,
    ) {
        self.value_names
            .update_algebraics(&self.algebraic_values, &values);
        self.algebraic_values = values;
    }
}

impl Default for ProofLocals {
    fn default() -> Self {
        Self {
            values: PersistentMap::default(),
            value_names: binding_names::BindingNames::default(),
            integer_values: PersistentMap::default(),
            algebraic_values: PersistentMap::default(),
            surface_facts: SurfacePropositionMap::default(),
            checked_lowerings: SurfacePropositionMap::default(),
            next_choice_variable: 3_000_000,
        }
    }
}

/// Execution data whose unchanged pieces can be shared by checked `Proof`
/// successors. Pure facts live in `ProofState::facts`; this contains only the
/// frontier state, certificate-construction metadata, and persistent branch provenance.
#[derive(Clone)]
pub(in crate::surface::proof) struct ExecutionProofPresentation {
    pub(in crate::surface::proof) loop_return_proofs: PersistentMap<usize, PlannedLoopReturns>,
    /// The immutable states recorded under program points or proof marks,
    /// which `at(selector, ...)` premises resolve against.
    pub(in crate::surface::proof) recorded_states: RecordedStates,
    /// The surface spellings this path has lowered, paired with their
    /// kernel propositions, so premises can be written as the source wrote
    /// them.
    pub(in crate::surface::proof) surface_propositions: SurfacePropositionMap,
    /// Declaration pairs returned by checked resource match/unfold. These
    /// are deliberately not unqualified lookup hints: a later C store may
    /// change the meaning of their written loads. Scoped citation is handled
    /// by the subsequent presentation-boundary repair.
    pub(in crate::surface::proof) resource_body_clauses:
        PersistentSequence<crate::surface::proof::resources::ResourceClausePresentation>,
    /// Case assumptions introduced on this path by proof-level splits.
    pub(in crate::surface::proof) case_assumptions: PersistentSequence<CaseAssumption>,
    /// The C `if` conditions this path took, in the order it took them, each
    /// spelled at the branching statement's entry state and carrying the
    /// polarity of the arm the path entered. A C branch the body took is as
    /// written as the loop guard is, so the smart invariant-bundle closer may
    /// name these too. The list is what execution recorded on this path; it
    /// is never a search over ambient facts, and a join restores the parent's
    /// list with the arms' entries dropped.
    pub(in crate::surface::proof) path_branch_premises: PersistentSequence<ClickProposition>,
    /// Frontier-local loop clauses, paired with the kernel-owned verified
    /// rules and migrated across joins as arm deltas.
    pub(in crate::surface::proof) frontier_loop_clauses: FrontierLoopClauses,
    /// Outcome tactics deferred during execution, applied in order at
    /// finalization; joins carry each arm's suffix.
    pub(in crate::surface::proof) post_execution_tactics:
        PersistentSequence<DeferredPostExecutionTactic>,
    /// Deferred source prefix already visited while preparing case obligations.
    pub(in crate::surface::proof) partitioned_post_execution_tactics:
        PersistentSequence<DeferredPostExecutionTactic>,
    /// Checked direct-call edge order for the narrow terminal int32 handler
    /// split. This is path-routing presentation, not proof evidence: each
    /// selected outcome retains its own kernel-checked theorem and goal.
    pub(in crate::surface::proof) call_outcome_edges: Option<Vec<bool>>,
    /// The path's surface record: certificate-visible certificate facts, the
    /// premise anchor, and proof-level case choices.
    pub(in crate::surface::proof) surface_record: SurfaceRecord,
    /// Where the checked `close_invariants` tactic sat, so the invariant
    /// bundle check its caller performs after the check finishes can be
    /// timed against that tactic's own identity instead of going unattributed.
    ///
    /// `close_invariants` only records the intent during check; the kernel
    /// re-derivation that gives it meaning runs in
    /// `verify_one_loop_preservation_proof` once the whole certificate has
    /// checked. Without this the dominant cost of the loop-invariant bundle
    /// carries no class tag at all (`git history (profiler coverage, 2026-07-31)`).
    pub(in crate::surface::proof) invariant_closer_step: Option<InvariantCloserStep>,
    /// Where a smart region-level invariant closer was written. Like the
    /// explicit closer above, this is expansion and timing attribution only;
    /// the kernel-owned invariant-closure flag carries semantic authority.
    pub(in crate::surface::proof) region_solve: Option<(usize, usize)>,
    /// Whether this execution lineage has explicitly unfolded a composite
    /// resource. Only that checked operation opts a frontier `have` into
    /// materializing one selected relation from the compact composition;
    /// call postconditions keep the relation lazy so source expansion retains
    /// their anchored rewrites.
    pub(in crate::surface::proof) resource_unfolded: bool,
    /// Where a source tactic's expansion is being captured on this path.
    pub(in crate::surface::proof) expansion: ExpansionCursor,
    pub(in crate::surface::proof) branch_path: PersistentSequence<String>,
    /// Kernel facts whose checked C-branch Surface spellings must survive a
    /// join for extraction and explicit historical premises.
    pub(in crate::surface::proof) branch_surface_facts: PersistentOrderedSet<Proposition>,
    /// Decisions on the currently focused branch execution lineage. Forks
    /// share history and add only the new decision and its index entry.
    branch_decisions: ExecutionBranchDecisions,
    /// Path-local provenance aligned with terminal execution candidates.
    /// Keeping each outcome's lineage, Surface lowerings, and recorded-state
    /// states in one record makes their correspondence structural rather
    /// than an invariant across parallel vectors. The record is output-sized
    /// Proof provenance; its persistent roots do not copy semantic state.
    outcome_provenance: crate::kernel::proof::PersistentVector<OutcomeProvenance>,
    outcome_fact_root: Option<Arc<ProofFacts>>,
    pub(in crate::surface::proof) checked_leaf_facts: Option<Arc<CheckedLeafFacts>>,
    /// The facts of the last checked statement with every effect the path
    /// has retained, extended step by step ([`EffectLeaf`]).
    pub(in crate::surface::proof) effect_leaf: Option<Arc<EffectLeaf>>,
    /// Exact producer-issued bindings for load-defining equations.  The
    /// vector is output-sized and persistent across proof forks; conflicting
    /// observations for one variable are retained as an ambiguity tombstone.
    pub(in crate::surface::proof) generated_load_bindings:
        PersistentMap<crate::kernel::Variable, crate::kernel::GeneratedLoadBinding>,
    /// Append-only producer observations. Joins consume only each arm's
    /// suffix since the split root, keeping merge work output-sized.
    pub(in crate::surface::proof) generated_load_binding_events:
        PersistentSequence<crate::kernel::GeneratedLoadBinding>,
    /// Exact source occurrences observed for generated load variables.  This
    /// is separate from the source-neutral binding map so a future source
    /// consumer can require both identities without changing kernel facts.
    pub(in crate::surface::proof) generated_load_source_resolutions:
        PersistentMap<crate::kernel::Variable, crate::kernel::GeneratedLoadSourceResolution>,
    /// Append-only source observations. Joins consume only each arm's suffix
    /// since the split root, just like generated-load binding observations.
    pub(in crate::surface::proof) generated_load_source_events:
        PersistentSequence<crate::kernel::GeneratedLoadSourceEvent>,
    /// The one selected existential whose body leaves may still be cited by
    /// an enclosing `extract`.  A later `choose` replaces this active record;
    /// nested `have`/scope boundaries start without one. This is
    /// presentation-only provenance: the kernel's exact conjunct index remains
    /// the authority for extraction.
    pub(in crate::surface::proof) chosen_projection: Option<ChosenProjection>,
    /// The fact list the last `loop` tactic on this path copied from the
    /// proof's facts, as it was copied. The next `loop` extends it by the
    /// facts the proof gained since (`PureFactList::extended_to_proof_facts`)
    /// instead of copying and indexing every fact again.
    pub(in crate::surface::proof) loop_fact_list: Option<crate::surface::PureFactList>,
    /// The environment the last `loop` tactic on this path stepped its rule
    /// under, before that rule: its claim's environment holding the frontier
    /// loop rules of `rules`. The next `loop` adds the rules since instead
    /// of copying every earlier rule into a new environment.
    pub(in crate::surface::proof) loop_rule_environment: Option<Arc<LoopRuleEnvironment>>,
    /// The annotation the last `loop` tactic on this path made of its
    /// function, with what it was made from, so the next `loop` lowers only
    /// its own loop when nothing else changed.
    pub(in crate::surface::proof) loop_annotation: Option<Arc<LoopAnnotationCache>>,
    /// A surface-stated existential can retain spellings of its checked body
    /// leaves without referring to a numbered contract requirement.
    pub(in crate::surface::proof) existential_projection: Option<ExistentialProjection>,
    /// Index disequalities the implicit tail's store search spelled but could
    /// not prove before a store that then dropped a cached cell. Diagnostic
    /// only: a later refusal reading that cell names the fact to state. Never
    /// read while checking.
    pub(in crate::surface::proof) store_separation_misses: PersistentSequence<StoreSeparationMiss>,
}

/// One cached cell a store dropped because the store search could not prove
/// the index disequality that keeps it. Everything here was constructed by
/// that search; a report prints it and searches nothing.
#[derive(Clone, Debug)]
pub(in crate::surface::proof) struct StoreSeparationMiss {
    /// The statement that ran, as a proof names it (`statement(5)`).
    pub(in crate::surface::proof) statement: String,
    /// The cached cell the store dropped.
    pub(in crate::surface::proof) cell: crate::kernel::Pointer,
    /// The dropped cell as the statement's C locals spell it, `q[0]`.
    pub(in crate::surface::proof) cell_text: Option<String>,
    /// The cell the store wrote.
    pub(in crate::surface::proof) store: crate::kernel::Pointer,
    /// The spelled disequality the search tried at the statement's pre-state.
    pub(in crate::surface::proof) fact: ClickProposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) struct ExistentialProjection {
    /// The checked body fact, not a numbered source clause, authorizes later
    /// proper-conjunct extraction.
    pub(in crate::surface::proof) chosen_body: Proposition,
    pub(in crate::surface::proof) chosen_name: String,
    pub(in crate::surface::proof) chosen_variable: crate::kernel::Variable,
    pub(in crate::surface::proof) source_memory_state: crate::kernel::MemoryStateIdentity,
    pub(in crate::surface::proof) leaves: Vec<ExistentialProjectionLeaf>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) struct ExistentialProjectionLeaf {
    pub(in crate::surface::proof) connective_path: Vec<usize>,
    pub(in crate::surface::proof) surface: ClickProposition,
    pub(in crate::surface::proof) kernel: Proposition,
}

/// Surface spellings for the checked leaves of a selected existential body.
/// The source requirement and state are retained alongside every checked
/// leaf so a spelling cannot silently drift to the current heap after a C
/// declaration.  This record is intentionally branch-local and is never a
/// proof fact in its own right.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) struct ChosenProjection {
    pub(in crate::surface::proof) source_id: RequirementSourceId,
    pub(in crate::surface::proof) principal_fact_index: usize,
    pub(in crate::surface::proof) source_token: ProjectionSourceToken,
    pub(in crate::surface::proof) source_proposition: ClickProposition,
    /// Exact source token selected before any checked predicate unfolding.
    pub(in crate::surface::proof) source_requirement: Proposition,
    /// The existential proposition after the active, checked unfolding path.
    pub(in crate::surface::proof) checked_source: Proposition,
    pub(in crate::surface::proof) chosen_name: String,
    pub(in crate::surface::proof) chosen_variable: crate::kernel::Variable,
    pub(in crate::surface::proof) source_memory_state: crate::kernel::MemoryStateIdentity,
    pub(in crate::surface::proof) source_selector: ProgramPointSelector,
    pub(in crate::surface::proof) leaves: Vec<ChosenProjectionLeaf>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) struct ChosenProjectionLeaf {
    pub(in crate::surface::proof) source_token: ProjectionSourceToken,
    pub(in crate::surface::proof) surface: ClickProposition,
    pub(in crate::surface::proof) kernel: Proposition,
}

pub(in crate::surface::proof) type ExecutionProofState =
    KernelProofExecutionState<ExecutionProofPresentation>;

impl ExecutionProofState {
    pub(in crate::surface::proof) fn loop_return_proof(
        &self,
        path_index: usize,
    ) -> Option<&Arc<LoopReturnProof>> {
        if let Some(proof) = self
            .presentation
            .outcome_provenance
            .get(path_index)
            .and_then(|p| p.loop_return.as_ref())
        {
            return Some(proof);
        }
        let (loop_index, return_index) = self.core.pending_loop_return_origin(path_index)?;
        self.presentation
            .loop_return_proofs
            .get(&loop_index)?
            .paths
            .get(return_index)
    }

    pub(in crate::surface::proof) fn record_terminal_loop_return_proofs(
        &mut self,
        returns: &[Arc<LoopReturnProof>],
    ) -> Result<(), ClickError> {
        let Some(execution) = self.core.frontier.execution() else {
            return Ok(());
        };
        let direct_paths = (0..execution.paths().len())
            .filter(|index| self.core.pending_loop_return_origin(*index).is_none())
            .count();
        if !returns.is_empty() && direct_paths != returns.len() {
            return Err(ClickError::new(
                "terminal loop return outcomes do not align with their preservation proofs",
            ));
        }
        let mut provenance = (0..execution.paths().len())
            .map(|index| self.provenance_for_outcome(index))
            .collect::<Vec<_>>();
        for (path, returned) in provenance.iter_mut().zip(returns) {
            path.loop_return = Some(returned.clone());
        }
        self.presentation.outcome_provenance = provenance.into();
        Ok(())
    }

    pub(super) fn retain_terminal_statement_cases(
        &mut self,
        cases: Vec<Vec<Proposition>>,
        state: ExecutionState,
        point: ProgramPointRef,
    ) {
        let state = Arc::new(state);
        self.presentation.outcome_provenance = cases
            .into_iter()
            .enumerate()
            .map(|(index, facts)| {
                let mut provenance = self.provenance_for_outcome(index);
                provenance.terminal_statement_case = Some(Arc::new(TerminalStatementCase {
                    facts,
                    state: state.clone(),
                    point: point.clone(),
                }));
                provenance
            })
            .collect::<Vec<_>>()
            .into();
    }

    fn provenance_for_outcome(&self, path_index: usize) -> OutcomeProvenance {
        self.presentation
            .outcome_provenance
            .get(path_index)
            .cloned()
            .unwrap_or_else(|| OutcomeProvenance {
                terminal_statement_case: None,
                checked_leaf_facts: self.presentation.checked_leaf_facts.clone(),
                loop_return: self.loop_return_proof(path_index).cloned(),
                call_routes: Vec::new(),
                branch_decisions: self.presentation.branch_decisions.clone(),
                match_arms: PersistentMap::default(),
                case_obligations: PersistentMap::default(),
                checked_haves: PersistentMap::default(),
                surface_propositions: self.presentation.surface_propositions.clone(),
                recorded_states: self.presentation.recorded_states.clone(),
                generated_load_bindings: self.presentation.generated_load_bindings.clone(),
            })
    }

    /// The read-only execution data lowering and fixed-state proofs consult.
    pub(in crate::surface::proof) fn view<'s>(
        &'s self,
        context: &'s ExecutionProofContext<'_>,
    ) -> ExecutionView<'s> {
        ExecutionView::new(
            &self.core.frontier,
            &self.core.effect_facts,
            &self.presentation.recorded_states,
            &self.presentation.surface_propositions,
            context.constants.function_entry_state.as_ref(),
        )
    }

    /// The execution state at a proof's entry: the frontier's C state and
    /// effect facts with no branch provenance yet.
    pub(in crate::surface::proof) fn at_entry(
        state: ExecutionState,
        frontier: ExecutionFrontier,
        recorded_states: RecordedStates,
        surface_propositions: SurfacePropositionMap,
        branch_path: PersistentSequence<String>,
    ) -> Self {
        Self::new(
            ExecutionProofCore::at_entry(state, frontier),
            ExecutionProofPresentation {
                loop_return_proofs: PersistentMap::default(),
                recorded_states,
                surface_propositions,
                resource_body_clauses: PersistentSequence::default(),
                case_assumptions: PersistentSequence::default(),
                path_branch_premises: PersistentSequence::default(),
                frontier_loop_clauses: FrontierLoopClauses::default(),
                post_execution_tactics: PersistentSequence::default(),
                partitioned_post_execution_tactics: PersistentSequence::default(),
                call_outcome_edges: None,
                surface_record: SurfaceRecord::default(),
                invariant_closer_step: Default::default(),
                region_solve: None,
                resource_unfolded: false,
                expansion: ExpansionCursor::default(),
                branch_path,
                branch_surface_facts: PersistentOrderedSet::default(),
                branch_decisions: ExecutionBranchDecisions::default(),
                outcome_provenance: Default::default(),
                outcome_fact_root: None,
                checked_leaf_facts: None,
                effect_leaf: None,
                generated_load_bindings: PersistentMap::default(),
                generated_load_binding_events: PersistentSequence::default(),
                generated_load_source_resolutions: PersistentMap::default(),
                generated_load_source_events: PersistentSequence::default(),
                chosen_projection: None,
                existential_projection: None,
                store_separation_misses: PersistentSequence::default(),
                loop_fact_list: None,
                loop_rule_environment: None,
                loop_annotation: None,
            },
        )
    }
}

/// A `loop` tactic's annotation of its function and the inputs it was made
/// from (`ExecutionProofPresentation::loop_annotation`). The block and the
/// parsed function are named by address: both are the claim's own, borrowed
/// for the whole proof.
/// A path's frontier-local loop clauses in binding order, with the loops
/// they bind indexed, so asking whether a loop already has one does not
/// walk every clause the earlier loops bound.
#[derive(Clone, Default)]
pub(in crate::surface::proof) struct FrontierLoopClauses {
    clauses: PersistentSequence<StructuralClause>,
    loops: crate::persistent::PersistentSet<usize>,
}

impl FrontierLoopClauses {
    pub(in crate::surface::proof) fn push(&mut self, clause: StructuralClause) {
        if let CodeRegion::Loop(index) = clause.region() {
            self.loops = self.loops.with_value(*index);
        }
        self.clauses.push(clause);
    }

    /// Whether some clause is bound to loop `index`.
    pub(in crate::surface::proof) fn binds_loop(&self, index: usize) -> bool {
        self.loops.contains(&index)
    }
}

impl std::ops::Deref for FrontierLoopClauses {
    type Target = PersistentSequence<StructuralClause>;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

pub(in crate::surface::proof) struct LoopAnnotationCache {
    pub(in crate::surface::proof) function_block: usize,
    pub(in crate::surface::proof) parsed_function: usize,
    pub(in crate::surface::proof) start_facts: Arc<crate::surface::PureFactList>,
    pub(in crate::surface::proof) function_entry_state: Option<ExecutionState>,
    pub(in crate::surface::proof) initial_state: ExecutionState,
    pub(in crate::surface::proof) arguments: Vec<ProgramExpression>,
    /// The frontier clauses bound before the annotated loop's own clause.
    pub(in crate::surface::proof) frontier_clauses: FrontierLoopClauses,
    /// The annotated loop's own clause, bound to it.
    pub(in crate::surface::proof) bound_clause: StructuralClause,
    /// The block the annotated loop was checked with: `frontier_clauses`,
    /// then `bound_clause`, then any nested clauses its proof bound.
    pub(in crate::surface::proof) bound_function_block: crate::surface::FunctionBlock,
    pub(in crate::surface::proof) bound_nested_clauses: bool,
    pub(in crate::surface::proof) annotation: crate::surface::lowering::LoopAnnotation,
}

/// A claim's execution environment extended by a path's frontier loop
/// rules (`ExecutionProofPresentation::loop_rule_environment`).
pub(in crate::surface::proof) struct LoopRuleEnvironment {
    pub(in crate::surface::proof) base: ExecutionEnvironment,
    pub(in crate::surface::proof) rules: PersistentSequence<crate::kernel::VerifiedLoopRule>,
    pub(in crate::surface::proof) environment: ExecutionEnvironment,
}

impl LoopRuleEnvironment {
    /// `base` holding `rules` in order, built from `cached` when that holds
    /// an earlier prefix of `rules` over the same base.
    pub(in crate::surface::proof) fn extending(
        cached: Option<&Self>,
        base: &ExecutionEnvironment,
        rules: &PersistentSequence<crate::kernel::VerifiedLoopRule>,
    ) -> Self {
        let environment = cached
            .filter(|cached| cached.base == *base)
            .and_then(|cached| {
                let added = rules.suffix_since(&cached.rules)?;
                Some(cached.environment.clone().with_verified_loop_rules(added))
            })
            .unwrap_or_else(|| base.clone().with_verified_loop_rules(rules.iter().cloned()));
        Self {
            base: base.clone(),
            rules: rules.clone(),
            environment,
        }
    }
}

#[derive(Clone)]
struct ExecutionBranchDecision {
    fingerprint: std::sync::OnceLock<u64>,
    condition: ClickProposition,
    value: bool,
}

/// Private identities distinguish terminal joins even when loop iterations
/// share identical source guards and program-point spellings.
fn new_terminal_execution_route() -> Result<usize, ClickError> {
    static NEXT_ROUTE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    NEXT_ROUTE
        .fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |next| next.checked_add(1),
        )
        .map_err(|_| ClickError::new("terminal execution route identities exhausted"))
}

/// Keeps source order for certificate stitching and an exact-condition index
/// for case selection. Looking up one condition never walks path history.
#[derive(Clone, Default)]
struct ExecutionBranchDecisions {
    ordered: PersistentSequence<ExecutionBranchDecision>,
    by_route: PersistentMap<usize, Arc<ExecutionBranchDecision>>,
    by_condition: PersistentMap<u64, Vec<Arc<ExecutionBranchDecision>>>,
}

impl ExecutionBranchDecisions {
    fn key(condition: &ClickProposition) -> u64 {
        use std::hash::{Hash, Hasher};
        struct CountedHasher(std::collections::hash_map::DefaultHasher);
        impl Hasher for CountedHasher {
            fn finish(&self) -> u64 {
                self.0.finish()
            }
            fn write(&mut self, bytes: &[u8]) {
                crate::instrumentation::record_deterministic_work(bytes.len());
                self.0.write(bytes);
            }
        }
        let mut hasher = CountedHasher(std::collections::hash_map::DefaultHasher::new());
        condition.hash(&mut hasher);
        hasher.finish()
    }

    fn push(&mut self, decision: ExecutionBranchDecision) {
        let key = *decision
            .fingerprint
            .get_or_init(|| Self::key(&decision.condition));
        let mut bucket = self.by_condition.get(&key).cloned().unwrap_or_default();
        // Fingerprints only select a bucket; exact syntax equality decides
        // membership and guards against hash collisions.
        if !bucket.iter().any(|existing| {
            existing.condition == decision.condition && existing.value == decision.value
        }) {
            bucket.push(Arc::new(decision.clone()));
            self.by_condition = self.by_condition.with_inserted(key, bucket);
        }
        self.ordered.push(decision);
    }

    #[cfg(test)]
    fn value(&self, condition: &ClickProposition) -> Result<Option<bool>, ClickError> {
        self.value_for_key(condition, Self::key(condition))
    }

    fn value_for_key(
        &self,
        condition: &ClickProposition,
        key: u64,
    ) -> Result<Option<bool>, ClickError> {
        let mut result = None;
        if let Some(bucket) = self.by_condition.get(&key) {
            for decision in bucket {
                if &decision.condition != condition {
                    continue;
                }
                if result.is_some_and(|value| value != decision.value) {
                    return Err(ClickError::new(
                        "checked execution path records both sides of the post-execution `if` condition"
                            .to_string(),
                    ));
                }
                result = Some(decision.value);
            }
        }
        Ok(result)
    }

    fn iter(&self) -> impl Iterator<Item = &ExecutionBranchDecision> {
        self.ordered.iter()
    }

    fn record_route(&mut self, route: usize, decision: Arc<ExecutionBranchDecision>) {
        self.by_route = self.by_route.with_inserted(route, decision);
    }

    fn value_for_route(
        &self,
        route: usize,
        condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        let decision = self
            .by_route
            .get(&route)
            .ok_or_else(|| ClickError::new("terminal cursor lost its checked execution route"))?;
        if &decision.condition != condition {
            return Err(ClickError::new(
                "terminal cursor names a different checked execution condition",
            ));
        }
        Ok(decision.value)
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.ordered.is_empty()
    }
}

/// Read-only terminal data borrowed from an execution `Proof` by claim
/// finalization. This view carries no transition methods and owns no semantic
/// state; the `Proof` remains alive as the sole authority while finalization
/// checks its typed outcome goals.
pub(super) struct ProofExecutionView<'p> {
    pub(super) state: &'p ExecutionState,
    pub(super) facts: &'p ProofFacts,
    pub(super) frontier: &'p ExecutionFrontier,
    pub(super) execution: &'p ExecutionProofState,
    pub(super) context: &'p ExecutionProofContext<'p>,
    pub(super) unfolded_predicates: &'p SharedVec<String>,
    pub(super) branch_path: &'p PersistentSequence<String>,
    outcome_provenance: &'p crate::kernel::proof::PersistentVector<OutcomeProvenance>,
}

impl ProofExecutionView<'_> {
    pub(super) fn terminal_statement_choices(
        &self,
        path_index: usize,
    ) -> Result<Vec<SurfacePathChoice>, String> {
        let Some(case) = self
            .outcome_provenance
            .get(path_index)
            .and_then(|path| path.terminal_statement_case.as_ref())
        else {
            return Ok(Vec::new());
        };
        case.facts
            .iter()
            .enumerate()
            .filter_map(|(index, fact)| {
                let Proposition::ConditionIs(condition, value) = fact else {
                    return None;
                };
                Some((|| {
                    let condition = synthesize_surface_proposition(
                        &Proposition::ConditionIs(condition.clone(), true),
                        self.context.parameter_binding(),
                        &case.state,
                    )
                    .ok_or_else(|| "terminal statement case has no Click spelling".to_string())?;
                    let condition = super::cursor_execution::surface_frozen_at_program_point(
                        &condition,
                        &case.point,
                    )
                    .map_err(|error| error.raw_summary().to_string())?;
                    Ok(SurfacePathChoice {
                        occurrence: usize::MAX - index,
                        selector: SurfacePathSelector::Proposition(condition),
                        value: *value,
                        tactic_offset: 0,
                    })
                })())
            })
            .collect()
    }

    /// Exact producer metadata for one terminal outcome. Terminal joins keep
    /// this per-outcome map because different arms may carry different
    /// observations; a non-branching frontier uses the shared presentation
    /// map directly.
    #[cfg(test)]
    pub(super) fn generated_load_bindings(
        &self,
        path_index: usize,
    ) -> &PersistentMap<crate::kernel::Variable, crate::kernel::GeneratedLoadBinding> {
        self.outcome_provenance
            .get(path_index)
            .map(|provenance| &provenance.generated_load_bindings)
            .unwrap_or(&self.execution.presentation.generated_load_bindings)
    }

    /// Selects the leaf of a retained surface certificate that one checked
    /// outcome reaches, following each terminal surface `if` the way
    /// [`append_surface_step_to_leaves`] does. Decisions are the same typed
    /// split provenance [`Self::surface_branch_path`] reads.
    pub(super) fn surface_step_branch_path(
        &self,
        path_index: usize,
        steps: &[ProofStep],
    ) -> Option<Vec<bool>> {
        let mut decisions = self
            .outcome_provenance
            .get(path_index)
            .map(|provenance| &provenance.branch_decisions)
            .unwrap_or(&self.execution.presentation.branch_decisions)
            .iter();
        let mut path = Vec::new();
        let mut current = super::execution_state::through_single_arm_matches(steps);
        while let Some(ProofStep::If {
            condition,
            then_proof,
            else_proof,
            ..
        }) = current.last()
        {
            let selected_then = decisions
                .find(|decision| decision.condition == *condition)?
                .value;
            path.push(selected_then);
            current = super::execution_state::through_single_arm_matches(if selected_then {
                then_proof.steps()
            } else {
                else_proof.steps()
            });
        }
        Some(path)
    }

    /// The proof-level case decisions recorded on one outcome path, in
    /// decision order: each is a surface condition and the arm taken.
    /// Selects the retained surface branch skeleton for one checked outcome.
    /// Decisions are Proof provenance recorded at the typed splits; expansion
    /// reads them without reconstructing semantic facts from the post-state.
    pub(super) fn surface_branch_path(
        &self,
        path_index: usize,
        tactics: &[ProofTactic],
    ) -> Option<Vec<bool>> {
        // Decisions are retained in decision order, outermost first, and the
        // skeleton is walked outermost first too. Consuming them in reverse
        // found the outer condition only after the inner ones had already
        // been skipped, so every path through more than one surface `if`
        // reported no branch path at all and its closer was stitched onto
        // every leaf instead of its own.
        let provenance = self.outcome_provenance.get(path_index);
        let mut decisions = provenance
            .map(|provenance| &provenance.branch_decisions)
            .unwrap_or(&self.execution.presentation.branch_decisions)
            .iter();
        let mut call_routes = provenance
            .map(|provenance| provenance.call_routes.as_slice())
            .unwrap_or(&[])
            .iter();
        let mut path = Vec::new();
        let mut current = tactics;
        loop {
            let Some(branch) = current
                .iter()
                .rev()
                .find(|tactic| matches!(tactic, ProofTactic::If(_) | ProofTactic::CallOutcomes(_)))
            else {
                return Some(path);
            };
            let (selected, next) = match branch {
                ProofTactic::If(proof_if) => {
                    let selected = decisions
                        .find(|decision| decision.condition == proof_if.condition)?
                        .value;
                    (
                        selected,
                        if selected {
                            &proof_if.then_tactics
                        } else {
                            &proof_if.else_tactics
                        },
                    )
                }
                ProofTactic::CallOutcomes(outcomes) => {
                    let returned = *call_routes.next()?;
                    (
                        returned,
                        if returned {
                            &outcomes.returned_tactics
                        } else {
                            &outcomes.threw_tactics
                        },
                    )
                }
                _ => unreachable!(),
            };
            path.push(selected);
            current = next;
        }
    }
}

/// A completing statement's published candidate, the facts it was checked
/// under, and whether those facts already hold every effect its path
/// retained, so an outcome goal need not import them again.
pub(in crate::surface::proof) type CheckedLeafFacts =
    (FunctionExecutionCandidate, ProofFacts, bool);

/// The facts a path's last checked statement held, with every effect the
/// path has retained. Each statement extends it by the facts it introduced
/// and the effects it retained, so a completed path's outcome goal reads it
/// instead of importing the path's whole effect history.
pub(in crate::surface::proof) struct EffectLeaf {
    /// The statement's own facts, the lineage the next statement extends.
    base: ProofFacts,
    pub(in crate::surface::proof) facts: ProofFacts,
    /// How many of the path's effects `facts` holds.
    effects: usize,
}

impl EffectLeaf {
    /// The leaf after a statement checked under `facts`, with the path's
    /// effects `effects`. A statement whose facts descend from the last
    /// leaf's adds only its own facts and new effects, unless they outnumber
    /// the effects a rebuild refolds; any other starts over.
    pub(in crate::surface::proof) fn after_statement(
        previous: Option<&Self>,
        facts: &ProofFacts,
        effects: &crate::kernel::ExecutionFacts,
    ) -> Self {
        let extended = previous.and_then(|previous| {
            // Rebuilding refolds the `previous.effects` effects the previous
            // leaf already holds; a larger delta (the facts a join or a long
            // run of cases added since that leaf) is cheaper to rebuild.
            let introduced = (previous.effects <= effects.len())
                .then(|| facts.introduced_since_within(&previous.base, previous.effects))
                .flatten()?;
            let leaf = introduced
                .into_iter()
                .fold(previous.facts.clone(), |leaf, fact| {
                    leaf.with_kernel_checked_fact(fact)
                });
            Some((leaf, previous.effects))
        });
        let (mut leaf, folded) = extended.unwrap_or_else(|| (facts.clone(), 0));
        for fact in effects.facts_from(folded) {
            leaf = leaf.with_kernel_checked_fact(fact.proposition().clone());
        }
        Self {
            base: facts.clone(),
            facts: leaf,
            effects: effects.len(),
        }
    }
}

/// Explicit case facts emitted by one terminal statement, in evaluation order.
/// Kept with each outcome so expansion can place different closers after a
/// single `step()` without reconstructing guards from ambient facts.
struct TerminalStatementCase {
    facts: Vec<Proposition>,
    state: Arc<ExecutionState>,
    point: ProgramPointRef,
}

#[derive(Clone)]
struct OutcomeProvenance {
    terminal_statement_case: Option<Arc<TerminalStatementCase>>,
    checked_leaf_facts: Option<Arc<CheckedLeafFacts>>,
    loop_return: Option<Arc<LoopReturnProof>>,
    /// The checked call edges selected on this terminal path, outermost
    /// `outcomes` first; `true` is `returned`. A surrounding branch can add
    /// paths that never visited a call, so this belongs to each outcome
    /// rather than to the joined frontier as one flat vector.
    call_routes: Vec<bool>,
    branch_decisions: ExecutionBranchDecisions,
    match_arms: OutcomeMatchArms,
    /// Ordinary exhaustiveness proofs completed before either case arm.
    case_obligations: PersistentMap<usize, Arc<ProofCertificate>>,
    /// Explicit source haves already checked while preparing a later split.
    checked_haves: PersistentMap<usize, Arc<ProofCertificate>>,
    surface_propositions: SurfacePropositionMap,
    recorded_states: RecordedStates,
    #[cfg_attr(not(test), allow(dead_code))]
    generated_load_bindings:
        PersistentMap<crate::kernel::Variable, crate::kernel::GeneratedLoadBinding>,
}

type Obligation = KernelBranchObligation<PropositionPresentation, Arc<OutcomeProofData>>;

type KernelProofHandle = KernelProofObject<ProofLocals, Obligation, ExecutionProofState>;
type PropositionObligation =
    KernelPropositionObligation<PropositionPresentation, Arc<OutcomeProofData>>;
type OutcomeObligation = FunctionOutcomeObligation<Arc<OutcomeProofData>>;

/// Opaque diagnostic view over the same persistent kernel handle used by the
/// checker. Formatting happens only when the terminal error message is read.
struct ProofDiagnosticProofState(
    KernelProofHandle,
    Arc<ProofNode>,
    Vec<(Variable, String)>,
    Option<ExecutionState>,
    Option<crate::surface::proof_trace::ChildArgumentTrace>,
    Option<(&'static str, Box<Proposition>, Option<String>)>,
    Option<crate::surface::proof_diagnostics::MemoryHistoryDiagnostic>,
    Option<Arc<crate::kernel::proof::RejectedResourceRewriteFact>>,
    Vec<(Variable, ProgramType)>,
    // The value the goal's `result` denotes, when the goal is about a
    // function outcome.
    Option<ProgramValue>,
    Vec<crate::kernel::ReadResolutionDiagnostic>,
    // The instance a refused `fold` proposed, when it keeps a hidden record,
    // so the refusal shows the record its failed body fact reads.
    Option<Arc<crate::kernel::ResourceInstance>>,
    &'static str,
    DiagnosticNaming,
    // The recorded states an outcome goal's `at(...)` cites. A shared
    // handle; the citable ones are selected only when a report is rendered.
    Option<crate::surface::RecordedStates>,
    // The function's source layout, so names registered after the proof has
    // unwound still spell a call's result as `<region>.result`.
    Option<crate::surface::lowering::SourceExecutionLayout>,
);

/// The names a captured diagnostic gives the proof's values: the naming
/// tables themselves, or what they are built from when the diagnostic is
/// rendered. A diagnostic is captured on every refused attempt and rendered
/// for few of them, so the deferred form holds shared handles and copies no
/// list of locals or parameters.
pub(in crate::surface::proof) enum DiagnosticNaming {
    Tables(
        Vec<crate::languages::interface::ImportedParameter>,
        Vec<ProgramExpression>,
    ),
    /// A state's locals, then the shared entry parameters and arguments.
    LocalsThenParameters(ExecutionState, Arc<crate::surface::ParameterNaming>),
}

impl DiagnosticNaming {
    fn register(&self, labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels) {
        match self {
            Self::Tables(names, values) => {
                labels.register_naming(ParameterBinding::new(names, values));
            }
            Self::LocalsThenParameters(state, naming) => {
                let (mut names, mut values) =
                    crate::surface::diagnostics::local_naming_tables(state);
                names.extend(naming.parameters.iter().cloned());
                values.extend(naming.arguments.iter().cloned());
                labels.register_naming(ParameterBinding::new(&names, &values));
            }
        }
    }
}

/// The C values the proof's own binders name: `let`, `choose`, `obtain`
/// and `unfold` bindings. Diagnostics and premise spelling both name values
/// through these, so a report and a citation agree.
fn proof_local_program_values(
    proof: &KernelProofHandle,
) -> impl Iterator<Item = (&str, &ProgramValue)> {
    proof
        .state()
        .locals()
        .values
        .iter()
        .filter_map(|(name, expression)| match expression {
            ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
                Some((name.as_str(), value))
            }
            _ => None,
        })
}

/// The C values the focused goal's `intro` binders name. Where a binder
/// shadows an outer name, an `outer.` entry spells that outer value.
fn goal_binder_program_values(
    proof: &KernelProofHandle,
) -> impl Iterator<Item = (&str, &ProgramValue)> {
    proof
        .state()
        .open_branches()
        .get(proof.focused_branch())
        .and_then(|branch| match &branch.obligation {
            Obligation::Proposition(goal) => Some(goal.presentation.surface_bindings.iter()),
            _ => None,
        })
        .into_iter()
        .flatten()
        .filter_map(|(name, expression)| match expression {
            ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
                Some((name.as_str(), value))
            }
            _ => None,
        })
}

impl Proof<'_> {
    /// Retain lexical names without enumerating unrelated proof bindings.
    pub(in crate::surface::proof) fn requirement_binder_name_scope(
        &self,
    ) -> super::surface_synthesis::ProofBindingNamesScope {
        let shadows = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => goal.surface_bindings.clone(),
            _ => PersistentMap::default(),
        };
        super::surface_synthesis::ProofBindingNamesScope::enter(
            self.state.locals().value_names.clone(),
            shadows,
        )
    }

    /// The kernel variables the proof's binders name, as synthesis reads
    /// them: scalar and algebraic binder values, and a pointer binder whose
    /// value is a symbolic block's base. The first map holds the goal's `intro`
    /// binders, which may shadow a C name and so are spelled before one; the
    /// second the proof's other binders, spelled where no C name holds the
    /// value. A proof local an `intro` binder shadows is out of scope.
    pub(in crate::surface::proof) fn binder_variable_names(
        &self,
    ) -> (BTreeMap<Variable, String>, BTreeMap<Variable, String>) {
        fn variable(value: &ProgramValue) -> Option<Variable> {
            match value.numeric_value() {
                ProgramValue::Parameter(term) => match term.node {
                    crate::kernel::AlgebraicTermNode::Variable(variable) => Some(variable),
                    _ => None,
                },
                crate::kernel::arithmetic_c_value!(MachineTerm::Variable(variable)) => {
                    Some(*variable)
                }
                ProgramValue::Pointer(pointer) => {
                    match (&pointer.pointer().block, &pointer.pointer().offset) {
                        (
                            crate::kernel::PointerBlock::Symbolic(variable),
                            PointerOffsetTerm::Constant(0),
                        ) => Some(*variable),
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        // A goal's `intro` binder shadows a proof local of the same name:
        // that local is out of scope, and its name now spells the binder.
        let shadowing = goal_binder_program_values(&self.state)
            .map(|(name, _)| name)
            .filter(|name| !name.starts_with("outer."))
            .collect::<BTreeSet<_>>();
        let named = |values: &mut dyn Iterator<Item = (&str, &ProgramValue)>| {
            values
                .filter_map(|(name, value)| Some((variable(value)?, name.to_owned())))
                .collect::<BTreeMap<_, _>>()
        };
        let mut intro = named(&mut goal_binder_program_values(&self.state));
        // An Integer proof local, such as a loop's `iterations` or an
        // `obtain`'s binder, names the variable it holds.
        for (name, value) in self.local_integer_values().iter() {
            if let crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::Variable(
                variable,
            )) = value
                && !shadowing.contains(name.as_str())
            {
                intro.entry(*variable).or_insert_with(|| name.clone());
            }
        }
        let locals = self
            .state
            .state()
            .locals()
            .values
            .iter()
            .filter(|(name, _)| !shadowing.contains(name.as_str()))
            .filter_map(|(name, expression)| {
                let variable = match expression {
                    ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
                        variable(value)?
                    }
                    ContractExpression::AlgebraicVariable { binder_index, .. } => {
                        crate::surface::lowering::algebraic_binder_variable(*binder_index).ok()?
                    }
                    _ => return None,
                };
                Some((variable, name.clone()))
            })
            .collect();
        (intro, locals)
    }
}

fn diagnostic_value_variable(value: &ProgramValue) -> Option<Variable> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Parameter(term) => match term.node {
            crate::kernel::AlgebraicTermNode::Variable(variable) => Some(variable),
            _ => None,
        },
        crate::kernel::arithmetic_c_value!(term) => match term {
            MachineTerm::Variable(variable) => Some(*variable),
            // A `Bool` binder (Stage 5), carried as its cast.
            MachineTerm::BoolCast { value, .. } => match value.as_ref() {
                crate::kernel::ConditionTerm::Variable(variable) => Some(*variable),
                _ => None,
            },
            _ => None,
        },
        ProgramValue::Pointer(pointer) => match &pointer.pointer().offset {
            PointerOffsetTerm::Variable(variable) => Some(*variable),
            // C pointers to sized elements keep their direct symbolic offset
            // in element units. An added displacement is composite and does
            // not identify the pointer local itself.
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => {
                value.operand_view().variable().copied()
            }
            _ => None,
        },
        ProgramValue::Void => None,
    }
}

/// How many recorded states a failure report consults for names.
const NAMED_STATE_LIMIT: usize = 32;

/// A value no current name holds, but a scalar local held at a recorded
/// state this path can cite, spells as `at(region(N).entry, x)`:
/// exactly the value `x` had there. The value a loop havocked for `i` is `i`
/// at the loop's own entry, so a body goal names it as the iteration's entry
/// value. Names the current state gives were registered first and win. Among
/// states, the oldest of the most recent [`NAMED_STATE_LIMIT`] wins,
/// which for a loop-carried value is the head that minted it. A read of a
/// state's memory is qualified by its point, and an address no structural
/// spelling names (a heap allocation after its local's frame ended) is the
/// pointer local that held it there, `at(region(2).exit, p)`. Diagnostics
/// only: this runs when a failure is printed, never while checking.
pub(in crate::surface::proof) fn register_recorded_state_names(
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
    retained_states: &crate::surface::RecordedStates,
) {
    labels.recorded_states(retained_states);
    register_state_names(labels, &citable_states(retained_states));
    // Each exited loop's pass count, `loop(i).iterations`.
    for (name, iterations) in retained_states.loop_iteration_bindings() {
        if let crate::kernel::IntegerTerm::Variable(variable) = iterations {
            labels.integer_source_name(*variable, name);
        }
    }
    // Each recorded call's result, `statement(0).call(f, 0).result`.
    for (spelling, value) in retained_states.call_result_bindings() {
        register_call_result_name(labels, spelling, value);
    }
}

/// A call's result is spelled by its call, `<call>.result`.
fn register_call_result_name(
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
    spelling: String,
    value: &ProgramValue,
) {
    match value.numeric_value() {
        crate::kernel::arithmetic_c_value!(MachineTerm::Variable(variable)) => {
            labels.fallback_source_name(*variable, spelling, value.program_type());
        }
        crate::kernel::arithmetic_c_value!(read @ MachineTerm::MemoryLoad(..)) => {
            labels.fallback_read_name(read, spelling);
        }
        ProgramValue::Pointer(pointer) => {
            labels.fallback_pointer_name(pointer.pointer(), spelling.clone());
            labels.fallback_value_name(spelling, value.clone());
        }
        _ => {}
    }
}

/// The most recent recorded states an `at(...)` can cite, oldest first,
/// then the proof's older marks, with the point each one is spelled by.
/// Each part is bounded by `NAMED_STATE_LIMIT`; each state shares its
/// persistent storage.
fn citable_states(
    retained_states: &crate::surface::RecordedStates,
) -> Vec<(String, ExecutionState)> {
    use crate::surface::{CodeRegionRef, ProgramPointRef, ProgramPointSelector};
    let recent = retained_states.recent(NAMED_STATE_LIMIT);
    // The proof's own marks stay citable however many statements ran since:
    // a long loop body pushes `mark iteration` out of the recent window, and
    // the iteration-entry values only it names would print as `<unnamed>`.
    // They come last, so a name the recent window gives still wins.
    let marks = retained_states
        .marks(NAMED_STATE_LIMIT)
        .into_iter()
        .filter(|(selector, _)| !recent.iter().any(|(known, _)| known == selector))
        .collect::<Vec<_>>();
    recent
        .into_iter()
        .rev()
        .chain(marks)
        // Only points `at(...)` resolves from recorded states.
        .filter(|(selector, _)| match selector {
            ProgramPointSelector::Mark(_) => true,
            ProgramPointSelector::ProgramPoint(ProgramPointRef { region, .. }) => matches!(
                region,
                CodeRegionRef::Region(_) | CodeRegionRef::Loop(_) | CodeRegionRef::Label(_)
            ),
        })
        .map(|(selector, state)| {
            (
                crate::surface::diagnostics::describe_program_point_selector(selector),
                state.clone(),
            )
        })
        .collect()
}

fn register_state_names(
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
    citable: &[(String, ExecutionState)],
) {
    // A read of a state's memory is spelled against the locals it held,
    // as `at(point, p[1])`.
    for (point, state) in citable {
        labels.source_state(state, point.clone());
    }
    for (point, state) in citable {
        for (name, stored) in state.locals().object_values() {
            let value = stored.native();
            let value = value.as_ref();
            // A pointer's offset variable is not the pointer; a scalar
            // local's value, or a pointer local's whole address, is exactly
            // the local.
            // A temporary the translation introduced has no source spelling.
            if name.starts_with("__click")
                || name.starts_with("__rust_")
                || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                continue;
            }
            let name = crate::surface::diagnostics::rust_variable_spelling(name)
                .unwrap_or_else(|| name.to_string());
            // A `usize` or `uintptr_t` local is a pointer integer; its
            // numeric value is the scalar the local held.
            match value.numeric_value() {
                crate::kernel::arithmetic_c_value!(MachineTerm::Variable(variable)) => {
                    // A read of a memory a recorded point names is spelled as
                    // that read, `old(g[0])`, which says where the value came
                    // from.
                    if crate::kernel::registered_load_for_variable(variable)
                        .is_some_and(|(memory, _)| labels.names_memory(memory.memory()))
                    {
                        continue;
                    }
                    labels.fallback_source_name(
                        *variable,
                        format!("at({point}, {name})"),
                        value.program_type(),
                    );
                }
                crate::kernel::arithmetic_c_value!(read @ MachineTerm::MemoryLoad(memory, _, _)) => {
                    if !labels.names_memory(memory.memory()) {
                        labels.fallback_read_name(read, format!("at({point}, {name})"));
                    }
                }
                // An address no structural spelling names, a heap
                // allocation, is the pointer local that held it.
                ProgramValue::Pointer(pointer) => {
                    labels.fallback_pointer_name(pointer.pointer(), format!("at({point}, {name})"));
                }
                _ => {}
            }
        }
    }
}

impl crate::surface::proof_diagnostics::ProofDiagnosticState for ProofDiagnosticProofState {
    fn register_names(
        &self,
        labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
    ) {
        let _spelling = self
            .15
            .as_ref()
            .map(crate::surface::diagnostics::SourcePathSpellingScope::enter);
        self.13.register(labels);
        for (variable, name) in &self.2 {
            labels.source_name(*variable, name.clone());
        }
        // A proof `let { result: r } = step(...)` holds the exact scalar result, so its
        // user-chosen name wins over the synthesized C assignment target.
        for (name, value) in proof_local_program_values(&self.0) {
            if let ProgramValue::Pointer(pointer) = value {
                labels.immutable_pointer_name(pointer.pointer(), name);
            }
            if let Some(variable) = diagnostic_value_variable(value) {
                labels.immutable_source_name(variable, name.to_owned());
                labels.source_type(variable, value.program_type());
            }
        }
        for (name, value) in self.0.state().locals().algebraic_values.iter() {
            if let crate::kernel::SpecAlgebraicExpressionNode::Variable(variable) = value.node {
                labels.source_name(variable, name.clone());
            }
        }
        for (name, value) in self.0.state().locals().integer_values.iter() {
            if let crate::kernel::SpecIntegerExpression::Term(
                crate::kernel::IntegerTerm::Variable(variable),
            ) = value
            {
                labels.integer_source_name(*variable, name.clone());
            }
        }
        // `intro` names a universal's binder on the goal it refines, not in
        // the proof's locals.
        // A report names a shadowed outer value by its source name.
        for (name, value) in
            goal_binder_program_values(&self.0).filter(|(name, _)| !name.starts_with("outer."))
        {
            if let Some(variable) = diagnostic_value_variable(value) {
                labels.source_name(variable, name.to_owned());
                labels.source_type(variable, value.program_type());
            }
        }
        if let Some(state) = &self.3 {
            labels.register_current_state(state);
        }
        if let Some(result) = &self.9 {
            labels.source_result(result);
        }
        for (variable, interface_type) in &self.8 {
            labels.source_type(*variable, *interface_type);
        }
        if let Some(branch) = self.0.state().open_branches().get(self.0.focused_branch())
            && let Some(execution) = branch.state.execution.as_deref()
        {
            if self.3.is_none() {
                labels.register_current_state(&execution.core.state);
                for (name, value) in execution.core.state.locals().object_values() {
                    if !name.starts_with("__rust_")
                        && let Some(variable) = diagnostic_value_variable(&value.native())
                    {
                        labels.source_name(
                            variable,
                            crate::surface::diagnostics::rust_variable_spelling(name)
                                .unwrap_or_else(|| name.to_string()),
                        );
                    }
                }
            }
            register_recorded_state_names(labels, &execution.presentation.recorded_states);
        }
        // An outcome goal's states name what a local held at a recorded
        // point, in the goal and the premises as in the proof context.
        if let Some(retained_states) = &self.14 {
            register_recorded_state_names(labels, retained_states);
        }
    }

    fn rejected_resource_fact(&self) -> Option<&crate::kernel::proof::RejectedResourceRewriteFact> {
        self.7.as_deref()
    }

    fn failed_requirement(&self) -> Option<(&str, &Proposition)> {
        self.5
            .as_ref()
            .map(|(label, fact, _)| (*label, fact.as_ref()))
    }

    fn proposed_hidden_record(&self) -> Option<&crate::kernel::ResourceInstance> {
        self.11.as_deref()
    }

    fn memory_history(
        &self,
    ) -> Option<&crate::surface::proof_diagnostics::MemoryHistoryDiagnostic> {
        self.6.as_ref()
    }

    fn read_resolutions(&self) -> &[crate::kernel::ReadResolutionDiagnostic] {
        &self.10
    }

    fn proof_context_kind(&self) -> Option<&str> {
        Some(self.12)
    }

    fn resources(&self) -> &[ResourceFact] {
        if let Some(state) = &self.3 {
            return state.resources().facts();
        }
        self.0
            .state()
            .open_branches()
            .get(self.0.focused_branch())
            .and_then(|branch| branch.state.execution.as_deref())
            .map_or(&[], |execution| execution.core.state.resources().facts())
    }

    fn kernel_goal(&self) -> Option<&Proposition> {
        let branch = self
            .0
            .state()
            .open_branches()
            .get(self.0.focused_branch())?;
        match &branch.obligation {
            Obligation::Proposition(goal) => Some(goal.proposition()),
            _ => None,
        }
    }

    fn premises(&self, limit: usize) -> Vec<&Proposition> {
        let Some(branch) = self.0.state().open_branches().get(self.0.focused_branch()) else {
            return Vec::new();
        };
        branch.state.facts.recent_facts(limit)
    }

    fn premise_count(&self) -> usize {
        self.0
            .state()
            .open_branches()
            .get(self.0.focused_branch())
            .map_or(0, |branch| branch.state.facts.fact_count())
    }

    fn proof_trace(
        &self,
        claim: &str,
        labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
        tactic_location: &dyn Fn(&[usize]) -> Option<(String, crate::source::SourcePosition)>,
        branch_arm: &dyn Fn(&[usize], &crate::source::SourcePosition) -> Option<usize>,
        have_body_contains: &dyn Fn(&[usize], &crate::source::SourcePosition) -> bool,
        target: Option<&crate::source::SourcePosition>,
        failing_path: Option<usize>,
    ) -> Option<String> {
        let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
        if !crate::surface::proof_trace::enabled_for(claim) {
            return None;
        }
        if let Some(branch) = self.0.state().open_branches().get(self.0.focused_branch())
            && let Some(execution) = branch.state.execution.as_deref()
        {
            labels.recorded_states(&execution.presentation.recorded_states);
            for (selector, state) in execution.presentation.recorded_states.recent(32) {
                labels.source_state(
                    state,
                    crate::surface::diagnostics::describe_program_point_selector(selector),
                );
            }
        }
        let lineage = trace_path_lineage(&self.1, self.0.focused_branch());
        let mut trace = crate::surface::proof_trace::render(
            claim,
            &lineage,
            labels,
            tactic_location,
            branch_arm,
            have_body_contains,
            target,
            failing_path,
        )?;
        if self
            .5
            .as_ref()
            .is_some_and(|(label, _, _)| *label == "rejected path fact")
        {
            trace = trace.replacen(
                "proof trace (checked tactics and branch facts)",
                "proof trace (checked prefix; certification failed)",
                1,
            );
        }
        if let Some(comparison) = &self.4 {
            comparison.append_to(&mut trace, labels);
        }
        crate::surface::proof_trace::append_legend(&mut trace, labels);
        Some(trace)
    }
}

/// Follow one goal through interleaved sibling steps. A structural join is
/// expanded later from its recorded checked arm lineages.
fn trace_path_lineage(
    node: &ProofNode,
    mut goal: BranchId,
) -> Vec<crate::surface::proof_trace::TracePathNode> {
    let mut lineage = Vec::new();
    let mut current = Some(node);
    while let Some(entry) = current {
        #[cfg(test)]
        crate::surface::proof_trace::record_lineage_visit();
        let selected_arm = if entry.step.is_some()
            || crate::surface::proof_trace::has_recorded_step(entry as *const ProofNode as usize)
        {
            if entry.focused_branch != goal {
                current = entry.parent.as_deref();
                continue;
            }
            None
        } else if entry.split_branches.contains(&goal) {
            let selected = goal;
            goal = entry.focused_branch;
            Some(selected)
        } else if entry.split_branches.is_empty() {
            goal = entry.focused_branch;
            None
        } else {
            current = entry.parent.as_deref();
            continue;
        };
        lineage.push(crate::surface::proof_trace::TracePathNode {
            node: entry as *const ProofNode as usize,
            selected_arm,
        });
        current = entry.parent.as_deref();
    }
    lineage.reverse();
    lineage
}

fn trace_arm_lineage(
    node: &ProofNode,
    marker: &Arc<ProofNode>,
    arm: BranchId,
) -> Vec<crate::surface::proof_trace::TracePathNode> {
    let mut lineage = Vec::new();
    let mut current = Some(node);
    while let Some(entry) = current {
        if std::ptr::eq(entry, marker.as_ref()) {
            break;
        }
        if entry.step.is_some() && entry.focused_branch == arm {
            lineage.push(crate::surface::proof_trace::TracePathNode {
                node: entry as *const ProofNode as usize,
                selected_arm: None,
            });
        }
        current = entry.parent.as_deref();
    }
    lineage.reverse();
    lineage
}

impl Proof<'_> {
    pub(in crate::surface::proof) fn record_accepted_trace(&self, claim: &str, path_index: usize) {
        if crate::surface::proof_trace::enabled_for(claim) {
            crate::surface::proof_trace::record_accepted_path(
                claim,
                path_index,
                false,
                trace_path_lineage(&self.node, self.focused_branch_id()),
                Box::new(self.node.clone()),
                Some(Box::new(self.diagnostic_state())),
            );
        }
    }

    /// Records this completed loop-phase path for the trace, under the path
    /// the enclosing proof had reached at the `loop` tactic.
    pub(in crate::surface::proof) fn record_nested_accepted_trace(
        &self,
        claim: &str,
        path_index: usize,
    ) {
        if crate::surface::proof_trace::enabled_for(claim) {
            crate::surface::proof_trace::record_accepted_path(
                claim,
                path_index,
                true,
                trace_path_lineage(&self.node, self.focused_branch_id()),
                Box::new(self.node.clone()),
                Some(Box::new(self.diagnostic_state())),
            );
        }
    }

    /// Retain the checked prefix of a written loop-phase arm that ran out
    /// of tactics. It can answer failure trace targets, but is not accepted.
    pub(in crate::surface::proof) fn record_unfinished_trace(
        &self,
        claim: &str,
        path_index: usize,
    ) {
        if crate::surface::proof_trace::enabled_for(claim) {
            crate::surface::proof_trace::record_unfinished_path(
                claim,
                path_index,
                trace_path_lineage(&self.node, self.focused_branch_id()),
                Box::new(self.node.clone()),
                Some(Box::new(self.diagnostic_state())),
            );
        }
    }

    pub(in crate::surface::proof) fn record_certification_failure_trace(
        &self,
        claim: &str,
        path_index: usize,
    ) {
        if crate::surface::proof_trace::enabled_for(claim) {
            crate::surface::proof_trace::record_certification_failure_path(
                claim,
                path_index,
                trace_path_lineage(&self.node, self.focused_branch_id()),
                Box::new(self.node.clone()),
                Some(Box::new(self.diagnostic_state())),
            );
        }
    }

    /// Certification keeps the actual theorem's names and checked lineage,
    /// even when its backing C function has a different name.
    pub(in crate::surface::proof) fn return_fold_certification_error(
        &self,
        message: String,
        rejected_fact: Option<Proposition>,
        path_index: usize,
    ) -> ClickError {
        self.record_certification_failure_trace(self.claim_label(), path_index);
        let mut state = self.diagnostic_state();
        state.5 = rejected_fact.map(|fact| ("rejected path fact", Box::new(fact), None));
        ClickError::with_diagnostic(
            message.clone(),
            crate::surface::proof_diagnostics::ProofFailureDiagnostic {
                failing_path: None,
                checks: None,
                origin: crate::surface::proof_diagnostics::ProofDiagnosticOrigin {
                    stage: "return-fold certification".into(),
                    location: self.claim_label().to_owned(),
                    source_tactic_path: None,
                },
                claim_label: self.claim_label().to_owned(),
                reason: message,
                state: Some(Arc::new(state)),
            },
        )
    }

    /// This proof's traced path so far, for a phase proof it is about to
    /// drive to render above its own.
    pub(in crate::surface::proof) fn trace_lineage(
        &self,
        claim: &str,
    ) -> Option<crate::surface::proof_trace::TraceLineage> {
        crate::surface::proof_trace::enabled_for(claim).then(|| {
            let node = self.node.clone();
            let branch = self.focused_branch_id();
            crate::surface::proof_trace::deferred_lineage(move || trace_path_lineage(&node, branch))
        })
    }

    /// Makes `parent_lineage` the traced path above this proof's root, as a
    /// `have` body's root is placed under the proof that opened it.
    pub(in crate::surface::proof) fn register_trace_scope_under(
        &self,
        parent_lineage: crate::surface::proof_trace::TraceLineage,
    ) {
        crate::surface::proof_trace::register_scope(
            Arc::as_ptr(&self.node) as usize,
            parent_lineage,
            Box::new(self.node.clone()),
        );
    }

    pub(in crate::surface::proof) fn note_trace_join_continuation_arm(&self, arm: Option<usize>) {
        if let Some(arm) = arm {
            crate::surface::proof_trace::set_join_continuation_arm(
                Arc::as_ptr(&self.node) as usize,
                arm,
            );
        }
    }

    /// Retain the checked proposition; all presentation happens at rendering.
    fn checked_trace_fact(&self, kernel: Proposition) -> crate::surface::proof_trace::TraceFact {
        crate::surface::proof_trace::TraceFact { kernel }
    }

    fn record_trace_branch(
        &self,
        marker: &Arc<ProofNode>,
        arms: [BranchId; 2],
        path_facts: &[Vec<Proposition>; 2],
        _condition: &ClickProposition,
    ) {
        if !crate::surface::proof_trace::enabled_for(self.claim_label()) {
            return;
        }
        self.record_trace_split(marker, arms, path_facts, "branch", ["then", "else"]);
    }

    /// Records a two-arm split for the trace: the tactic that opened it, how
    /// its arms are spelled, and the checked facts each arm assumes.
    fn record_trace_split(
        &self,
        marker: &Arc<ProofNode>,
        arms: [BranchId; 2],
        path_facts: &[Vec<Proposition>; 2],
        kind: &str,
        arm_names: [&'static str; 2],
    ) {
        if !crate::surface::proof_trace::enabled_for(self.claim_label()) {
            return;
        }
        let location = self
            .site()
            .path()
            .unwrap_or_else(|| format!("checked branch {}", marker.depth));
        let facts = |index: usize| {
            path_facts[index]
                .iter()
                .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact))
                .take(8)
                .cloned()
                .map(|kernel| crate::surface::proof_trace::TraceFact { kernel })
                .collect()
        };
        crate::surface::proof_trace::record_branch(
            Arc::as_ptr(marker) as usize,
            crate::surface::proof_trace::TraceBranch {
                header: format!("{location}: {kind}"),
                source_tactic_path: self.site().source_tactic_path(),
                arm_names,
                arms: [(arms[0], facts(0)), (arms[1], facts(1))],
            },
        );
    }

    fn record_trace_program_branch(
        &self,
        marker: &Arc<ProofNode>,
        arms: [Option<BranchId>; 2],
        path_facts: &[Option<Vec<Proposition>>; 2],
    ) {
        if !crate::surface::proof_trace::enabled_for(self.claim_label()) {
            return;
        }
        let [Some(then_id), Some(else_id)] = arms else {
            return;
        };
        let location = self
            .site()
            .path()
            .unwrap_or_else(|| "checked branch".into());
        let facts = |index: usize| {
            let focused = arms[index].and_then(|arm| self.focus_branch(arm).ok());
            path_facts[index]
                .as_ref()
                .into_iter()
                .flatten()
                .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact))
                .take(8)
                .cloned()
                .map(|kernel| {
                    if let Some(proof) = &focused {
                        proof.checked_trace_fact(kernel)
                    } else {
                        crate::surface::proof_trace::TraceFact { kernel }
                    }
                })
                .collect()
        };
        crate::surface::proof_trace::record_branch(
            Arc::as_ptr(marker) as usize,
            crate::surface::proof_trace::TraceBranch {
                header: format!("{location}: branch"),
                source_tactic_path: self.site().source_tactic_path(),
                arm_names: ["then", "else"],
                arms: [(then_id, facts(0)), (else_id, facts(1))],
            },
        );
    }
}

impl Proof<'_> {
    /// `proposition` spelled for a refusal's own text, with the names the
    /// report's `goal:` line uses for the same variables.
    pub(in crate::surface::proof) fn render_diagnostic_proposition(
        &self,
        proposition: &Proposition,
    ) -> String {
        use crate::surface::proof_diagnostics::ProofDiagnosticState as _;
        use crate::surface::proof_diagnostics::render;
        let mut labels = render::MemoryStateLabels::ambient();
        self.diagnostic_state().register_names(&mut labels);
        let mut text = render::render_proposition_labeled(proposition, &mut labels);
        text.push_str(&labels.trace_legend());
        text
    }

    fn diagnostic_state(&self) -> ProofDiagnosticProofState {
        // Pure theorem names have no ExecutionState from which the renderer can
        // recover their signedness. Retain types alongside those names.
        let mut source_types = match self.context.as_ref() {
            ProofContext::Pure(context) => context
                .theorem_context
                .values
                .values()
                .filter_map(|value| {
                    diagnostic_value_variable(value)
                        .map(|variable| (variable, value.program_type()))
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        let result = match self.context.as_ref() {
            ProofContext::FixedState(context) => context.fixed_state.result,
            _ => self
                .outcome_fixed_state_view()
                .and_then(|view| view.fixed_state.result),
        };
        source_types.extend(result.and_then(|value| {
            diagnostic_value_variable(value).map(|variable| (variable, value.program_type()))
        }));
        let source_names = match self.context.as_ref() {
            ProofContext::Pure(context) => {
                let mut names: Vec<_> = context
                    .theorem_context
                    .values
                    .iter()
                    .filter_map(|(name, value)| {
                        diagnostic_value_variable(value).map(|variable| (variable, name.clone()))
                    })
                    .collect();
                names.extend(context.theorem_context.diagnostic_names.iter().cloned());
                names.extend(
                    context
                        .theorem_context
                        .declaration_bindings
                        .iter()
                        .filter_map(|(name, expression)| {
                            let ContractExpression::AlgebraicVariable { binder_index, .. } =
                                expression
                            else {
                                return None;
                            };
                            crate::surface::lowering::algebraic_binder_variable(*binder_index)
                                .ok()
                                .map(|variable| (variable, name.clone()))
                        }),
                );
                names
            }
            ProofContext::FixedState(_) | ProofContext::Execution(_) => Vec::new(),
        };
        // Capture only a bounded diagnostic comparison while this proof's
        // arena and bridging mode are still active. The terminal renderer
        // must not recompute it after the verifier has unwound.
        let history = self.goal().and_then(|goal| {
            if !crate::kernel::resource_tracker::reads_any_resource(goal) {
                return None;
            }
            let names = self
                .outcome_fixed_state_view()
                .or_else(|| self.execution_fixed_state_view());
            let (parameters, arguments) = names
                .as_ref()
                .map(|view| {
                    (
                        view.parameter_binding.parameters,
                        view.parameter_binding.arguments,
                    )
                })
                .unwrap_or((&[], &[]));
            let premises = self
                .state
                .state()
                .open_branches()
                .get(self.state.focused_branch())
                .map(|branch| branch.state.facts.recent_facts(8))
                .unwrap_or_default();
            crate::surface::diagnostics::proposition_version_explanation(
                goal,
                &premises,
                ParameterBinding::new(parameters, arguments),
            )
            .map(|(explanation, _)| (self.store_separation_miss(&explanation), explanation))
            .or_else(|| {
                self.store_separation_miss_for_goal(goal)
                    .map(|(miss, explanation)| (Some(miss), explanation))
            })
            .map(|(miss, explanation)| {
                let miss = miss.map(|miss| crate::surface::proof_diagnostics::StoreSearchMiss {
                    statement: miss.statement,
                    cell: miss.cell_text,
                    fact: crate::surface::printing::source_click_proposition(&miss.fact),
                });
                let mut history =
                    crate::surface::proof_diagnostics::MemoryHistoryDiagnostic::capture(
                        explanation,
                    );
                history.store_search_miss = miss;
                history
            })
        });
        ProofDiagnosticProofState(
            self.state.clone(),
            self.node.clone(),
            source_names,
            match self.context.as_ref() {
                // Fixed-state subproofs have no execution branch, but their
                // live locals still name the values their goals contain.
                // ExecutionState shares its persistent storage; no environment is copied.
                ProofContext::FixedState(context) => Some(context.fixed_state.state.clone()),
                // The execution branch may still be the pre-execution root.
                // An outcome goal carries the authoritative post-state,
                // including permissions consumed or produced by its calls.
                ProofContext::Execution(_) => self
                    .outcome_fixed_state_view()
                    .map(|view| view.fixed_state.state.clone()),
                ProofContext::Pure(_) => None,
            },
            None,
            None,
            history,
            None,
            source_types,
            result.cloned(),
            Vec::new(),
            None,
            self.proof_context_description(),
            self.diagnostic_naming(),
            match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => {
                    Some(context.fixed_state.recorded_states.clone())
                }
                ProofContext::Execution(_) => self
                    .outcome_fixed_state_view()
                    .map(|view| view.fixed_state.recorded_states.clone()),
            },
            crate::surface::diagnostics::spelling_layout(),
        )
    }
}

/// The fixed-state data a result-aware checker consumes, resolved from
/// either a fixed-state proof's borrowed context or a focused function-outcome
/// goal (see [`Proof::outcome_fixed_state_view`]).
/// Which effect-availability context an outcome-goal fixed-state operation
/// consumes; each migrated tactic matches its legacy drain input exactly.
#[derive(Clone, Copy)]
pub(in crate::surface::proof) enum OutcomeEffectContext {
    Path,
    Frontier,
}

#[derive(Clone, Copy)]
pub(in crate::surface::proof) struct FixedStateOperationView<'p> {
    pub(in crate::surface::proof) claim_label: &'p str,
    pub(in crate::surface::proof) tactic_index: usize,
    pub(in crate::surface::proof) effect_facts: &'p ExecutionFacts,
    pub(in crate::surface::proof) parameter_binding: ParameterBinding<'p>,
    pub(in crate::surface::proof) fixed_state: FixedStateFrame<'p>,
    pub(in crate::surface::proof) surface_propositions: &'p SurfacePropositionMap,
    pub(in crate::surface::proof) spec_definitions: SpecDefinitions<'p>,
    pub(in crate::surface::proof) theorem_environment: &'p TheoremEnvironment,
    pub(in crate::surface::proof) original_requirements: &'p [Requirement],
    pub(in crate::surface::proof) requirement_facts: FixedStateFacts<'p>,
}

impl<'p> FixedStateOperationView<'p> {
    pub(in crate::surface::proof) fn from_fixed_state(
        context: &'p FixedStateProofContext<'_>,
    ) -> Self {
        Self {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: &context.effect_facts,
            parameter_binding: context.parameter_binding,
            fixed_state: context.fixed_state,
            surface_propositions: context.surface_propositions,
            spec_definitions: SpecDefinitions::new(
                context.spec_definitions.predicates,
                context.spec_definitions.functions,
            ),
            theorem_environment: context.theorem_environment,
            original_requirements: context.original_requirements,
            requirement_facts: context.requirement_facts,
        }
    }
}

/// One path-local function-outcome judgment: the checked return outcome of
/// one execution path awaiting its result-dependent continuations.
///
/// The goal owns the path's result value, post-outcome C state, and fact
/// context, and borrows the function-exit frontier's state by identity
/// for lowering. Result and effect operations will consume these goals
/// directly instead of converting through a mutable execution-context adapter.
/// The result-aware data one function outcome supplies to fixed-state operations:
/// its checked return value, post-outcome state, recorded surface
/// lowerings, and effect-availability facts.
#[derive(Clone)]
pub(in crate::surface::proof) struct OutcomeProofPresentation {
    pub(in crate::surface::proof) surface_propositions: SurfacePropositionMap,
    pub(in crate::surface::proof) recorded_states: RecordedStates,
    /// The statement-entry anchor for premises naming a C local after it
    /// left scope, captured from the frontier at derivation.
    pub(in crate::surface::proof) premise_anchor: Option<ProgramPointRef>,
    /// The lowered function-requirement facts in declaration order, captured
    /// as the raw prefix of the drain's working set at derivation: `choose`
    /// selects its source by requirement index, which persistent
    /// deduplication would misalign.
    /// Original proposition requirements keyed by their checked entry fact.
    /// Typed outcome evidence uses this persistent index to recover an exact
    /// function-entry Surface premise without scanning unrelated facts.
    pub(in crate::surface::proof) requirement_surfaces:
        Arc<PersistentMap<Proposition, ClickProposition>>,
    branch_decisions: ExecutionBranchDecisions,
    /// The checked call edges this outcome took, outermost `outcomes`
    /// first. `true` is `returned`; `false` is `threw`.
    pub(in crate::surface::proof) call_routes: Vec<bool>,
    /// The arm each `match` deferred after execution took on this path, by
    /// the match's source occurrence, with that arm's field bindings.
    pub(in crate::surface::proof) match_arms: OutcomeMatchArms,
    pub(in crate::surface::proof) case_obligations: PersistentMap<usize, Arc<ProofCertificate>>,
    pub(in crate::surface::proof) checked_haves: PersistentMap<usize, Arc<ProofCertificate>>,
}

/// The arm a deferred `match` took on one outcome path, by the match's
/// source occurrence: its index among the written arms and its bindings.
pub(in crate::surface::proof) type OutcomeMatchArms =
    PersistentMap<usize, (usize, PersistentMap<String, ContractExpression>)>;

pub(in crate::surface::proof) type OutcomeProofData =
    KernelOutcomeProofState<OutcomeProofPresentation>;

type BranchState = ProofBranchState<ExecutionProofState>;
type OpenBranch = ProofBranch<Obligation, ExecutionProofState>;

/// One proposition judgment keeps its checked kernel meaning and, when the
/// judgment originated in Surface Click, the exact syntax needed to refine
/// structural goals. Both values belong to the same immutable Proof state;
/// smart search must not carry a second caller-owned description of its goal.
#[derive(Clone, Default)]
pub(in crate::surface::proof) struct PropositionPresentation {
    pub(in crate::surface::proof) surface: Option<Arc<ClickProposition>>,
    /// The producer synthesized this display for an existing kernel goal.
    /// Its logical children may keep their kernel goals without a spelling;
    /// a user-written claim still requires exact presentation correspondence.
    pub(in crate::surface::proof) generated_surface: bool,
    /// Surface names introduced while refining this exact proposition goal.
    /// Universal binders are goal-local: sibling goals share the persistent
    /// map root at a split, then refine independently without leaking names.
    pub(in crate::surface::proof) surface_bindings: PersistentMap<String, ContractExpression>,
    /// What the kernel lowering recorded about this goal's outermost nodes.
    /// An introduction reads it instead of inferring the Surface-to-kernel
    /// correspondence from a shape the written syntax happens to share.
    pub(in crate::surface::proof) introductions: GoalIntroductions,
    /// The antecedents this goal's own introductions added to its fact
    /// context, each retained as the checked Surface-to-kernel pair the
    /// introduction consumed, plus the structural conjuncts of that pair.
    /// A later citation of one of these facts reads the retained kernel
    /// proposition instead of re-lowering the written antecedent under the
    /// fact context the introduction changed.
    pub(in crate::surface::proof) introduced_antecedents: IntroducedAntecedents,
    /// Checked per-child lowering records for a kernel conjunction assembled
    /// by the loop invariant body. The records retain the exact head chain
    /// that may wrap each child; they are consumed only by `both` when the
    /// generated Surface spelling needs that chain's written body.
    pub(in crate::surface::proof) both_children: Option<Arc<[BothChildPresentation; 2]>>,
    /// Exact kernel parent retained by a checked witness refinement when its
    /// substituted Surface body cannot be lowered independently.
    pub(in crate::surface::proof) witness_refinement_kernel: Option<Proposition>,
}

#[derive(Clone)]
pub(in crate::surface::proof) struct BothChildPresentation {
    pub(in crate::surface::proof) kernel: Proposition,
    pub(in crate::surface::proof) surface: Option<ClickProposition>,
    pub(in crate::surface::proof) introductions: Arc<crate::kernel::LoweringIntroductions>,
}

/// The head chain the kernel lowering recorded for one goal, and how much of
/// it this goal's introductions have already consumed.
///
/// The default is the unrecorded state: a goal whose kernel proposition did
/// not come from a lowering performed for it (a recorded correspondence, a
/// kernel-built obligation) has no head chain, and an introduction on it
/// falls back to refining the written Surface goal structurally.
#[derive(Clone, Default)]
pub(in crate::surface::proof) struct GoalIntroductions {
    recorded: Option<Arc<crate::kernel::LoweringIntroductions>>,
    consumed: usize,
}

impl GoalIntroductions {
    pub(in crate::surface::proof) fn recorded(
        introductions: crate::kernel::LoweringIntroductions,
    ) -> Self {
        Self {
            recorded: Some(Arc::new(introductions)),
            consumed: 0,
        }
    }

    pub(in crate::surface::proof) fn from_lowering(
        introductions: Option<crate::kernel::LoweringIntroductions>,
    ) -> Self {
        introductions.map_or_else(Self::default, Self::recorded)
    }

    /// The node an introduction would reach next, when this goal's lowering
    /// recorded one. Indexed access: no scan of the chain.
    pub(in crate::surface::proof) fn head(&self) -> Option<&crate::kernel::LoweringIntroduction> {
        self.recorded.as_ref()?.get(self.consumed)
    }

    /// The same chain with its head consumed. The recorded vector is shared,
    /// so advancing costs one clone of an `Arc` and an index.
    pub(in crate::surface::proof) fn advanced(&self) -> Self {
        Self {
            recorded: self.recorded.clone(),
            consumed: self.consumed.saturating_add(1),
        }
    }
}

/// Checked Surface-to-kernel antecedent pairs retained by introductions on
/// one goal, bucketed by a deterministic rendering of the Surface form. The
/// bucket keeps the written form so a citation is accepted only on exact
/// Surface equality, never on a rendering collision.
pub(in crate::surface::proof) type IntroducedAntecedents =
    PersistentMap<String, Arc<Vec<(ClickProposition, Proposition)>>>;

/// The retained kernel form of `surface`, when an introduction on this goal
/// added it. Work is one indexed lookup plus exact comparison inside the
/// selected bucket.
pub(in crate::surface::proof) fn retained_introduced_antecedent<'a>(
    retained: &'a IntroducedAntecedents,
    surface: &ClickProposition,
) -> Option<&'a Proposition> {
    retained
        .get(&format!("{surface:?}"))?
        .iter()
        .find_map(|(written, kernel)| (written == surface).then_some(kernel))
}

/// Records one checked Surface-to-kernel antecedent pair and every
/// structural conjunct pair it refines to. Refinement descends only where
/// the written conjunction and the kernel conjunction agree, so each
/// recorded pair remains an exact account of the introduction.
pub(in crate::surface::proof) fn retain_introduced_antecedent(
    retained: &IntroducedAntecedents,
    surface: &ClickProposition,
    kernel: &Proposition,
) -> IntroducedAntecedents {
    let key = format!("{surface:?}");
    let mut bucket = retained
        .get(&key)
        .map_or_else(Vec::new, |bucket| bucket.as_ref().clone());
    let retained = if bucket
        .iter()
        .any(|(written, recorded)| written == surface && recorded == kernel)
    {
        retained.clone()
    } else {
        bucket.push((surface.clone(), kernel.clone()));
        retained.with_inserted(key, Arc::new(bucket))
    };
    match (kernel, surface_logical_children(surface, true)) {
        (Proposition::And(left, right), Some((surface_left, surface_right))) => {
            let retained = retain_introduced_antecedent(&retained, &surface_left, left);
            retain_introduced_antecedent(&retained, &surface_right, right)
        }
        _ => retained,
    }
}

impl KernelPropositionObligation<PropositionPresentation, Arc<OutcomeProofData>> {
    fn kernel(&self) -> &Proposition {
        self.proposition()
    }
}

trait OpenBranchConstruction {
    fn proposition_in(state: BranchState, kernel: Proposition) -> Self;
    fn frontier(state: BranchState) -> Self;
    fn function_outcome(obligation: OutcomeObligation, state: BranchState) -> Self;
    fn surface_proposition_in(
        state: BranchState,
        kernel: Proposition,
        surface: ClickProposition,
    ) -> Self;
    fn surface_proposition_at_outcome(
        state: BranchState,
        outcome: Arc<OutcomeProofData>,
        kernel: Proposition,
        surface: ClickProposition,
    ) -> Self;
}

impl OpenBranchConstruction for OpenBranch {
    fn proposition_in(state: BranchState, kernel: Proposition) -> Self {
        Self::new(
            Obligation::Proposition(PropositionObligation::new(
                kernel,
                PropositionPresentation {
                    surface: None,
                    surface_bindings: PersistentMap::default(),
                    ..PropositionPresentation::default()
                },
            )),
            state,
        )
    }

    fn frontier(state: BranchState) -> Self {
        Self::new(Obligation::Frontier(FrontierObligation), state)
    }

    fn function_outcome(obligation: OutcomeObligation, state: BranchState) -> Self {
        Self::new(Obligation::FunctionOutcome(obligation), state)
    }

    fn surface_proposition_in(
        state: BranchState,
        kernel: Proposition,
        surface: ClickProposition,
    ) -> Self {
        Self::new(
            Obligation::Proposition(PropositionObligation::new(
                kernel,
                PropositionPresentation {
                    surface: Some(Arc::new(surface)),
                    surface_bindings: PersistentMap::default(),
                    ..PropositionPresentation::default()
                },
            )),
            state,
        )
    }

    /// A surface proposition judgment stated at one function outcome,
    /// borrowing that outcome's result-aware proof data by identity.
    fn surface_proposition_at_outcome(
        state: BranchState,
        outcome: Arc<OutcomeProofData>,
        kernel: Proposition,
        surface: ClickProposition,
    ) -> Self {
        Self::new(
            Obligation::Proposition(PropositionObligation::at_outcome(
                kernel,
                PropositionPresentation {
                    surface: Some(Arc::new(surface)),
                    surface_bindings: PersistentMap::default(),
                    ..PropositionPresentation::default()
                },
                outcome,
            )),
            state,
        )
    }
}

/// An equality with an `old(...)` or `at(label, ...)` operand can use that
/// state expression's reflexivity as an explicit transport source. Keep
/// this selector intentionally syntactic: the fixed-state checker remains the
/// authority for whether execution effects and result provenance permit the
/// transport.
pub(in crate::surface::proof) fn old_reflexive_transport_source(
    goal: &ClickProposition,
) -> Option<ClickProposition> {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = goal
    else {
        return None;
    };
    // An `old(..)` side first, then a side read at a marked program point:
    // either names the earlier state the other side's reads frame to.
    let old = match (left, right) {
        (_, ContractExpression::Old(_)) => right,
        (ContractExpression::Old(_), _) => left,
        (_, ContractExpression::At { .. }) => right,
        (ContractExpression::At { .. }, _) => left,
        _ => return None,
    };
    Some(ClickProposition::Comparison {
        left: old.clone(),
        operator: ComparisonOperator::Equal,
        right: old.clone(),
    })
}

impl<'a> Proof<'a> {
    fn with_kernel_state(&self, state: KernelProofHandle) -> Self {
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        }
    }

    /// Dev-only `sorry`: closes the focused proposition goal as admitted,
    /// without checking it. The caller records an admission; admitted results
    /// never verify in the gate. Requires the kernel flag (set solely by
    /// `click verify --allow-sorry`).
    pub(in crate::surface::proof) fn admit_focused_goal_for_sorry(
        &self,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .admit_focused_proposition_for_sorry()
            .ok_or_else(|| {
                self.step_error(
                    "`sorry` needs an open proposition goal to admit; it is only allowed as a complete `have` body",
                )
            })?;
        Ok(self.with_kernel_state(state))
    }

    fn state(&self) -> &ProofState {
        self.state.state()
    }

    /// The proof's Integer locals, with each loop the focused path has left
    /// binding its pass count as `loop(i).iterations`.
    pub(super) fn local_integer_values(
        &self,
    ) -> PersistentMap<String, crate::kernel::SpecIntegerExpression> {
        let mut values = self.state().locals().integer_values.clone();
        if let Some(execution) = self.execution() {
            for (name, iterations) in execution
                .presentation
                .recorded_states
                .loop_iteration_bindings()
            {
                values.insert(
                    name,
                    crate::kernel::SpecIntegerExpression::Term(iterations.clone()),
                );
            }
        }
        values
    }

    pub(super) fn local_algebraic_values(
        &self,
    ) -> &PersistentMap<String, crate::kernel::SpecAlgebraicExpression> {
        &self.state().locals().algebraic_values
    }

    /// The written forms of facts a pure proof introduced; see
    /// `ProofLocals::surface_facts`.
    pub(super) fn local_surface_facts(&self) -> &SurfacePropositionMap {
        &self.state().locals().surface_facts
    }

    /// Records `surface` as the written form of the checked `kernel` fact
    /// for later premise lookups in a pure proof.
    pub(super) fn with_local_surface_fact(
        &self,
        surface: &ClickProposition,
        kernel: &Proposition,
    ) -> Result<Self, ClickError> {
        let mut locals = self.state.locals().clone();
        locals.surface_facts.record_lowering(surface, kernel)?;
        Ok(self.with_kernel_state(self.state.with_locals(locals)))
    }

    fn focused_branch_id(&self) -> BranchId {
        self.state.focused_branch()
    }

    /// The open branch addressed by this handle. Focus is only a cursor;
    /// sibling branches remain in the same immutable proof state.
    fn focused_branch(&self) -> Option<&OpenBranch> {
        self.state().open_branches().get(self.focused_branch_id())
    }

    fn focused_obligation(&self) -> Option<&Obligation> {
        Some(&self.focused_branch()?.obligation)
    }

    fn checked_fact_transition(
        &self,
        locals: ProofLocals,
        facts: ProofFacts,
        complete: bool,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> CheckedFocusedTransition {
        let branch = (!complete).then(|| {
            self.focused_branch()
                .expect("a checked fact transition requires an open branch")
                .with_state(self.refined_branch_state(facts))
        });
        CheckedFocusedTransition::replacing(locals, branch, added_facts, checked_facts)
    }

    /// Installs one resource separation selected from the compact composition
    /// authority into this local checked proof state. The materialization is
    /// an internal premise-selection operation, not a user-visible proof
    /// step; enclosing scopes publish only their stated proposition.
    pub(super) fn materialize_selected_resource_separation(
        &self,
        goal: &Proposition,
    ) -> Option<Self> {
        let facts = self.facts().with_selected_resource_separation(goal);
        if facts.contains(goal) && !self.facts().contains(goal) {
            let transition = self.checked_fact_transition(
                self.state().locals().clone(),
                facts,
                false,
                vec![goal.clone()],
                vec![goal.clone()],
            );
            let state = self.publish_checked_transition(transition).ok()?;
            Some(self.with_kernel_state(state))
        } else {
            Some(self.clone())
        }
    }

    fn checked_execution_transition(
        &self,
        facts: ProofFacts,
        complete: bool,
        execution: ExecutionProofState,
        added_facts: Vec<Proposition>,
        checked_facts: Vec<Proposition>,
    ) -> CheckedFocusedTransition {
        let branch = (!complete).then(|| {
            let mut state = self.refined_branch_state(facts);
            state.execution = Some(Arc::new(execution));
            self.focused_branch()
                .expect("a checked execution transition requires an open branch")
                .with_state(state)
        });
        CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            branch,
            added_facts,
            checked_facts,
        )
    }

    fn publish_checked_transition(
        &self,
        transition: CheckedFocusedTransition,
    ) -> Result<KernelProofHandle, ClickError> {
        self.state
            .publish_checked_result(
                transition.locals,
                transition.branch,
                transition.added_facts,
                transition.checked_facts,
            )
            .map_err(|_| self.step_error("checked transition lost its focused proof branch"))
    }

    pub(in crate::surface::proof) fn proposition_obligation(
        &self,
    ) -> Option<&PropositionObligation> {
        match self.focused_obligation()? {
            Obligation::Proposition(goal) => Some(goal),
            _ => None,
        }
    }

    pub(in crate::surface::proof) fn local_binding(
        &self,
        name: &String,
    ) -> Option<&ContractExpression> {
        self.state().locals().values.get(name)
    }

    /// Every proof local in scope at this point, by name: a proof `match`
    /// arm's bindings, `let { ... } = unfold(...)` names, call-result binders, loop
    /// binders. Loop clauses written in this scope are resolved through it.
    pub(in crate::surface::proof) fn proof_local_values(
        &self,
    ) -> BTreeMap<String, ContractExpression> {
        self.state()
            .locals()
            .values
            .iter()
            .map(|(name, value)| (name.clone(), value.clone()))
            .collect()
    }

    /// Whether the obligation this handle addresses has been discharged. On
    /// a single-goal proof this coincides with completion; inside a sibling
    /// split, only the focused branch obligation's discharge is an arm's success —
    /// the sibling legitimately remains open.
    pub(super) fn focused_discharged(&self) -> bool {
        self.state()
            .open_branches()
            .get(self.focused_branch_id())
            .is_none()
    }

    /// The focused branch branch's path-local execution state, shared by identity
    /// with the frontier that created it.
    fn branch_execution(&self) -> Option<&Arc<ExecutionProofState>> {
        self.focused_branch()?.state.execution.as_ref()
    }

    /// The focused branch branch's path-local unfold delta.
    pub(in crate::surface::proof) fn focused_branch_unfolds(
        &self,
    ) -> &PersistentOrderedSet<String> {
        &self
            .focused_branch()
            .expect("unfold queries require an open goal")
            .state
            .unfolded_predicates
    }

    /// The focused branch goal's path-local fact context. Every caller is a
    /// checked operation or search query on an open goal: `apply_step` and
    /// the structural operations reject discharged proofs first.
    pub(in crate::surface::proof) fn facts(&self) -> &ProofFacts {
        match self.focused_branch() {
            Some(branch) => &branch.state.facts,
            None => unreachable!("fact queries require an open goal"),
        }
    }

    /// The focused branch goal's context with updated facts, for refinement rules
    /// that change goal content and facts together.
    fn refined_branch_state(&self, facts: ProofFacts) -> BranchState {
        BranchState {
            facts,
            unfolded_predicates: self.focused_branch_unfolds().clone(),
            execution: self.branch_execution().cloned(),
        }
    }

    /// Rebuilds the focused branch proposition judgment with new content under the
    /// given context, preserving any outcome proof data the judgment
    /// borrowed: a refinement changes what is claimed, never where it was
    /// stated.
    fn refined_proposition(
        &self,
        state: BranchState,
        kernel: Proposition,
        surface: Option<ClickProposition>,
        witness_refinement: bool,
    ) -> OpenBranch {
        let outcome = self.refinement_outcome();
        let surface = surface.or_else(|| self.spelled_goal(&kernel));
        let presentation =
            self.refinement_presentation(surface, witness_refinement.then(|| kernel.clone()));
        let obligation = match outcome {
            Some(outcome) => PropositionObligation::at_outcome(kernel, presentation, outcome),
            None => PropositionObligation::new(kernel, presentation),
        };
        OpenBranch::new(Obligation::Proposition(obligation), state)
    }

    /// The spelling of a refined goal no written template carries over to:
    /// the premise speller's, which lowers back to exactly `goal`. A goal is
    /// stated at the current state, so it is spelled with no premise anchor
    /// and never searches recorded states. Smart refinements reconstruct
    /// their structural goal from indexed source names, without premise search.
    /// Written refinements retain the existing premise presentation support.
    pub(in crate::surface::proof) fn spelled_goal(
        &self,
        goal: &Proposition,
    ) -> Option<ClickProposition> {
        if crate::instrumentation::smart_tactic_active() {
            return self.structural_goal_spelling(goal);
        }
        let recorded = (self).premise_surface_facts()?;
        crate::kernel::search::ProofSearch::available_surface_fact(self, recorded, None, goal)
            .or_else(|| {
                crate::kernel::search::ProofSearch::available_surface_fact(
                    self,
                    self.local_surface_facts(),
                    None,
                    goal,
                )
            })
    }

    /// Structural presentation from indexed names. Planning may use this for
    /// private query shapes; actual goals still pass the exact lowering check.
    pub(in crate::surface::proof) fn structural_proposition_candidate(
        &self,
        goal: &Proposition,
    ) -> Option<ClickProposition> {
        use super::surface_synthesis as synthesis;
        let _qualified = (self)
            .premise_surface_facts()
            .map(synthesis::QualifiedSynthesisScope::enter);
        synthesis::with_structural_goal_synthesis(|| match self.context.as_ref() {
            ProofContext::Pure(context) => synthesis::synthesize_surface_proposition_with_names(
                goal,
                ParameterBinding::new(&[], &[]),
                &context.source_state,
                &context.source_names,
            ),
            ProofContext::FixedState(context) => {
                let _points = synthesis::SynthesisRecordedPointsScope::enter(
                    context.fixed_state.recorded_states,
                );
                synthesis::synthesize_surface_proposition_at_entry_and_post(
                    goal,
                    context.parameter_binding,
                    context.fixed_state.pre_state,
                    context.fixed_state.state,
                )
            }
            ProofContext::Execution(_) => {
                let view = self.premise_fixed_state_view()?;
                let _points = synthesis::SynthesisRecordedPointsScope::enter(
                    view.fixed_state.recorded_states,
                );
                synthesis::synthesize_surface_proposition_at_entry_and_post(
                    goal,
                    view.parameter_binding,
                    view.fixed_state.pre_state,
                    view.fixed_state.state,
                )
            }
        })
    }

    fn structural_goal_spelling(&self, goal: &Proposition) -> Option<ClickProposition> {
        let candidate = self.structural_proposition_candidate(goal)?;
        // This compares presentation, not proof authority: rewriting already
        // produced the successor. A spelling must retain its exact term.
        self.lower_surface_proposition_direct(&candidate, "structural goal spelling")
            .ok()
            .filter(|lowered| lowered == goal)
            .map(|_| candidate)
    }

    fn refinement_outcome(&self) -> Option<Arc<OutcomeProofData>> {
        match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => goal.outcome.clone(),
            Some(Obligation::FunctionOutcome(goal)) => Some(goal.data.clone()),
            _ => None,
        }
    }

    fn refinement_presentation(
        &self,
        surface: Option<ClickProposition>,
        witness_refinement_kernel: Option<Proposition>,
    ) -> PropositionPresentation {
        // A refinement replaces the claim, so the head chain the lowering
        // recorded no longer describes it; the goal-local binders and the
        // antecedents its own introductions retained still do, because the
        // refinement changed neither the binder scope nor the fact context.
        match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => PropositionPresentation {
                surface: surface.map(Arc::new),
                surface_bindings: goal.surface_bindings.clone(),
                generated_surface: goal.generated_surface,
                introductions: GoalIntroductions::default(),
                introduced_antecedents: goal.introduced_antecedents.clone(),
                both_children: None,
                witness_refinement_kernel,
            },
            _ => PropositionPresentation {
                surface: surface.map(Arc::new),
                witness_refinement_kernel,
                ..PropositionPresentation::default()
            },
        }
    }

    /// The execution proof's per-proof context, when this is one.
    pub(in crate::surface::proof) fn execution_context(
        &self,
    ) -> Option<&ExecutionProofContext<'a>> {
        match self.context.as_ref() {
            ProofContext::Execution(context) => Some(context),
            _ => None,
        }
    }

    pub(in crate::surface::proof) fn execution(&self) -> Option<&ExecutionProofState> {
        self.branch_execution().map(Arc::as_ref)
    }

    #[cfg(test)]
    fn branches_next_id(&self) -> u64 {
        self.state().open_branches().next_id_for_test()
    }

    #[cfg(test)]
    fn outcome_result(&self) -> Option<&ProgramValue> {
        match self.focused_obligation()? {
            Obligation::FunctionOutcome(goal) => Some(goal.data.core.result.as_ref()),
            _ => None,
        }
    }

    pub(super) fn goal(&self) -> Option<&Proposition> {
        match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => Some(goal.kernel()),
            _ => None,
        }
    }

    pub(in crate::surface::proof) fn surface_goal(&self) -> Option<&ClickProposition> {
        match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => goal.surface.as_deref(),
            _ => None,
        }
    }

    /// Focuses a kernel proposition goal without a surface spelling; tests
    /// use it to address a goal directly.
    #[cfg(test)]
    pub(super) fn focus_fixed_state_goal(&self, goal: Proposition) -> Result<Self, ClickError> {
        self.focus_fixed_state_goal_with_surface(goal, None)
    }

    pub(super) fn focus_fixed_state_goal_with_surface(
        &self,
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
    ) -> Result<Self, ClickError> {
        self.focus_fixed_state_goal_for_claim(goal, surface_goal, None)
    }

    /// Focuses `goal` as a new proposition proof. With `claim_goal`, the
    /// obligation is the kernel's goal for a contract claim and keeps that
    /// claim's identity.
    pub(super) fn focus_fixed_state_goal_for_claim(
        &self,
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
        claim_goal: Option<&crate::kernel::ContractClaimGoal>,
    ) -> Result<Self, ClickError> {
        let fixed_state_context = matches!(self.context.as_ref(), ProofContext::FixedState(_))
            && matches!(self.focused_obligation(), Some(Obligation::Frontier(_)));
        // A function-outcome goal is itself a result-aware fixed-state proof context:
        // an externally owned obligation focused branch from it borrows the
        // outcome's proof data by identity, exactly like a nested `have`.
        let outcome = match self.focused_obligation() {
            Some(Obligation::FunctionOutcome(outcome_goal)) => Some(outcome_goal.data.clone()),
            _ => None,
        };
        if !fixed_state_context && outcome.is_none() {
            return Err(self.step_error(
                "a proposition obligation can be focused only from a fixed-state proof context",
            ));
        }
        let focused = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: if let Some(claim_goal) = claim_goal {
                self.state
                    .focus_contract_claim(
                        claim_goal,
                        PropositionPresentation {
                            surface: surface_goal.clone().map(Arc::new),
                            surface_bindings: PersistentMap::default(),
                            ..PropositionPresentation::default()
                        },
                    )
                    .map_err(|pending| match pending.first() {
                        Some(obligation) => self
                            .step_error_with_requirement(
                                "contract claim has an outstanding evaluation requirement",
                                None,
                                Some((
                                    "evaluation requirement",
                                    Box::new(obligation.proposition().clone()),
                                    None,
                                )),
                            )
                            .with_unresolved_requirement(obligation),
                        None => self
                            .step_error("contract claim has an outstanding evaluation requirement"),
                    })?
            } else {
                // Focusing a goal does not prove it. Its written or implicit
                // proof applies the selected partition rule explicitly.
                let facts = self.facts().clone();
                KernelProofObject::root(self.state().locals().clone(), {
                    let context = BranchState {
                        facts,
                        unfolded_predicates: self.focused_branch_unfolds().clone(),
                        execution: match &outcome {
                            Some(_) => self.branch_execution().cloned(),
                            None => None,
                        },
                    };
                    let presentation = PropositionPresentation {
                        surface: surface_goal.map(Arc::new),
                        surface_bindings: PersistentMap::default(),
                        ..PropositionPresentation::default()
                    };
                    let obligation = match outcome.clone() {
                        Some(outcome) => {
                            PropositionObligation::at_outcome(goal, presentation, outcome)
                        }
                        None => PropositionObligation::new(goal, presentation),
                    };
                    OpenBranch::new(Obligation::Proposition(obligation), context)
                })
            },
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
                split_branches: Vec::new(),
            }),
        };
        // Focusing changes the semantic root, but the checked trace prefix
        // still belongs to the context from which this goal was selected.
        if let Some(lineage) = self.trace_lineage(self.claim_label()) {
            focused.register_trace_scope_under(lineage);
        }
        Ok(focused)
    }

    /// Lowers and selects one externally owned Surface Click obligation from
    /// a fixed-state proof context. The returned proof shares every accumulated checked
    /// fact but owns fresh provenance for that obligation's closing steps.
    pub(super) fn focus_fixed_state_surface_goal(
        &self,
        goal: &ClickProposition,
    ) -> Result<Self, ClickError> {
        let kernel = self.lower_surface_goal(goal, "fixed-state obligation")?;
        self.focus_fixed_state_goal_with_surface(kernel, Some(goal.clone()))
    }

    pub(super) fn is_complete(&self) -> bool {
        self.state.is_complete()
    }

    /// Extracts Surface provenance only after the kernel has witnessed that
    /// every checked obligation is discharged.
    pub(super) fn completed_certificate(&self) -> Result<ProofCertificate, ClickError> {
        self.state
            .completion()
            .ok_or_else(|| self.step_error("cannot finalize a proof with open obligations"))?;
        Ok(self.certificate())
    }

    /// Extracts the exact semantic root discharged by this completed proof.
    /// Unlike the surface certificate, this authority is constructed and
    /// checked by the kernel proof object.
    pub(super) fn completed_proposition(
        &self,
    ) -> Result<crate::kernel::proof::CheckedProposition, ClickError> {
        self.state
            .completed_proposition()
            .ok_or_else(|| self.step_error("completed proof is not a proposition judgment"))
    }

    pub(in crate::surface::proof) fn active_unfolded_predicates(&self) -> Vec<String> {
        let inherited = match self.context.as_ref() {
            ProofContext::Pure(_) => &[][..],
            ProofContext::FixedState(context) => context.unfolded_predicates,
            ProofContext::Execution(_) => self
                .execution()
                .map(|execution| execution.core.unfolded_predicates.as_slice())
                .unwrap_or(&[]),
        };
        let mut names = inherited.to_vec();
        let mut seen = inherited.iter().cloned().collect::<BTreeSet<_>>();
        for name in self.focused_branch_unfolds() {
            if seen.insert(name.clone()) {
                names.push(name.clone());
            }
        }
        names
    }

    pub(super) fn certificate(&self) -> ProofCertificate {
        self.certificate_after_node(None)
            .expect("checked provenance reaches its own root and records only certificate steps")
    }

    /// Retains an output-sensitive certificate suffix from an exact ancestor.
    ///
    /// Pointer identity, rather than structural equality, proves ancestry.
    /// A similarly shaped proof from another root or checking context cannot
    /// be spliced into this derivation.
    pub(super) fn certificate_since(
        &self,
        checkpoint: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        if !Arc::ptr_eq(&self.context, &checkpoint.context) {
            return Err(
                self.step_error("certificate checkpoint belongs to a different proof context")
            );
        }
        self.certificate_after_node(Some(&checkpoint.node))
    }

    /// Captures the current provenance position without sharing semantic
    /// execution state.
    pub(super) fn checkpoint(&self) -> ProofCheckpoint<'a> {
        ProofCheckpoint {
            context: self.context.clone(),
            node: self.node.clone(),
        }
    }

    fn apply_contradiction(
        &self,
        surface: &ClickProposition,
    ) -> Result<KernelProofHandle, ClickError> {
        let fact = self.lower_cited_surface_proposition(surface, "`contradiction` fact")?;
        self.state
            .apply_contradiction(&fact)
            .map_err(|error| match error {
                PropositionCloseError::ContradictionUnavailable { fact_held } => {
                    let written = crate::surface::diagnostics::describe_click_proposition(surface);
                    let missing = if fact_held {
                        format!("`{written}` is available, but neither `not ({written})` nor its opposite comparison is")
                    } else {
                        format!("`{written}` itself is not an available fact")
                    };
                    self.step_error(format!(
                        "`contradiction({written})` requires an exact fact and its exact negation or opposite condition polarity: {missing}"
                    ))
                }
                PropositionCloseError::Unavailable => {
                    self.step_error("`contradiction` requires an open proof branch")
                }
                _ => unreachable!("kernel returned an unrelated contradiction error"),
            })
    }

    fn proposition_goal(&self, message: &str) -> Result<&Proposition, ClickError> {
        self.goal().ok_or_else(|| self.step_error(message))
    }

    fn proof_context_description(&self) -> &'static str {
        match self.context.as_ref() {
            ProofContext::Pure(_) => "pure proposition proof",
            ProofContext::FixedState(_) => "fixed-state proposition proof",
            ProofContext::Execution(_) if self.goal().is_some() => {
                "proposition proof at a fixed C execution state"
            }
            ProofContext::Execution(_) => "C execution proof",
        }
    }

    pub(in crate::surface::proof) fn unsupported_operation_error(&self, name: &str) -> ClickError {
        let context = self.proof_context_description();
        let reason = if self.goal().is_some() && matches!(name, "execute" | "step_until" | "step") {
            "this proof establishes a proposition; C execution cannot advance inside it"
        } else {
            "this operation is not available in this proof context"
        };
        self.step_error(format!(
            "unsupported proof operation `{name}` in a {context}: {reason}"
        ))
    }

    fn require_execution_frontier(&self, operation: &str) -> Result<(), ClickError> {
        matches!(self.focused_obligation(), Some(Obligation::Frontier(_)))
            .then_some(())
            .ok_or_else(|| {
                self.step_error(format!(
                    "{operation} cannot advance C execution inside a proposition proof"
                ))
            })
    }

    pub(in crate::surface::proof) fn claim_label(&self) -> &str {
        self.context.claim_label()
    }

    /// Names the failing step by where the user wrote it: the source tactic
    /// occurrence, then each enclosing `have`/`open` block's own position.
    /// When no driver attributed a source position (a planner-generated or
    /// searched script), it names the failing step's place in the checked
    /// lineage of the current block instead. The proof-tree depth is never
    /// reported as if it were a step number.
    pub(in crate::surface::proof) fn step_error(&self, message: impl Into<String>) -> ClickError {
        self.step_error_with_requirement(message, None, None)
    }

    fn step_error_resource_rewrite(
        &self,
        error: crate::kernel::proof::ResourceRewriteCheckError,
    ) -> ClickError {
        self.step_error_with_details(error.message, None, None, error.rejected_fact, Vec::new())
    }

    fn step_error_with_requirement(
        &self,
        message: impl Into<String>,
        comparison: Option<crate::surface::proof_trace::ChildArgumentTrace>,
        requirement: Option<(&'static str, Box<Proposition>, Option<String>)>,
    ) -> ClickError {
        self.step_error_with_details(message, comparison, requirement, None, Vec::new())
    }

    /// A refused `fold` of an instance that keeps a hidden record: the
    /// failed body fact, with the record the fold proposed beside it.
    pub(in crate::surface::proof) fn step_error_with_proposed_record(
        &self,
        message: impl Into<String>,
        comparison: Option<crate::surface::proof_trace::ChildArgumentTrace>,
        requirement: Option<(&'static str, Box<Proposition>, Option<String>)>,
        proposed: Option<Arc<crate::kernel::ResourceInstance>>,
    ) -> ClickError {
        self.step_error_with_state(message, comparison, requirement, None, Vec::new(), proposed)
    }

    fn step_error_with_details(
        &self,
        message: impl Into<String>,
        comparison: Option<crate::surface::proof_trace::ChildArgumentTrace>,
        requirement: Option<(&'static str, Box<Proposition>, Option<String>)>,
        rejected: Option<Arc<crate::kernel::proof::RejectedResourceRewriteFact>>,
        read_resolutions: Vec<crate::kernel::ReadResolutionDiagnostic>,
    ) -> ClickError {
        self.step_error_with_state(
            message,
            comparison,
            requirement,
            rejected,
            read_resolutions,
            None,
        )
    }

    fn step_error_with_state(
        &self,
        message: impl Into<String>,
        comparison: Option<crate::surface::proof_trace::ChildArgumentTrace>,
        requirement: Option<(&'static str, Box<Proposition>, Option<String>)>,
        rejected: Option<Arc<crate::kernel::proof::RejectedResourceRewriteFact>>,
        read_resolutions: Vec<crate::kernel::ReadResolutionDiagnostic>,
        proposed: Option<Arc<crate::kernel::ResourceInstance>>,
    ) -> ClickError {
        let reason = message.into();
        let mut diagnostic_state = self.diagnostic_state();
        diagnostic_state.4 = comparison;
        diagnostic_state.5 = requirement;
        diagnostic_state.7 = rejected;
        diagnostic_state.10 = read_resolutions;
        diagnostic_state.11 = proposed;
        let location = self
            .site
            .path()
            .unwrap_or_else(|| format!("checked step {}", self.node.depth + 1));
        let summary = format!(
            "`{}` proof step {}: {}",
            self.context.claim_label(),
            location,
            reason
        );
        let diagnostic = crate::surface::proof_diagnostics::ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: crate::surface::proof_diagnostics::ProofDiagnosticOrigin {
                stage: "proof step".to_owned(),
                location,
                source_tactic_path: self.site.source_tactic_path(),
            },
            claim_label: self.context.claim_label().to_owned(),
            reason,
            state: Some(Arc::new(diagnostic_state)),
        };
        ClickError::with_diagnostic(summary, diagnostic)
    }

    /// Preserve the goal already carried by a completed transport when its
    /// caller notices exhaustion during the remaining source bookkeeping.
    pub(in crate::surface::proof) fn attach_transport_budget_diagnostic(
        &self,
        error: ClickError,
        completed: &Self,
    ) -> ClickError {
        let [_, target] = completed.state().checked_facts() else {
            return self.attach_step_diagnostic(error);
        };
        self.step_error_with_requirement(
            error.raw_summary(),
            None,
            Some(("checked transport target", Box::new(target.clone()), None)),
        )
    }

    pub(in crate::surface::proof) fn attach_step_diagnostic(
        &self,
        error: ClickError,
    ) -> ClickError {
        if !matches!(
            error.kind(),
            crate::surface::ClickErrorKind::Proof | crate::surface::ClickErrorKind::Internal
        ) || error.proof_claim_label().is_some()
        {
            return error;
        }
        let location = self
            .site
            .path()
            .unwrap_or_else(|| format!("checked step {}", self.node.depth + 1));
        let diagnostic = crate::surface::proof_diagnostics::ProofFailureDiagnostic {
            failing_path: None,
            checks: None,
            origin: crate::surface::proof_diagnostics::ProofDiagnosticOrigin {
                stage: "proof step".to_owned(),
                location,
                source_tactic_path: self.site.source_tactic_path(),
            },
            claim_label: self.context.claim_label().to_owned(),
            reason: error.raw_summary().to_owned(),
            state: Some(Arc::new(self.diagnostic_state())),
        };
        error.with_diagnostic_if_missing(diagnostic)
    }

    /// The step position this proof's diagnostics report.
    pub(in crate::surface::proof) fn site(&self) -> &ProofStepSite {
        &self.site
    }

    /// The same proof, attributing its next step to the claim's `index`th
    /// source tactic occurrence. This is diagnostic addressing only: no goal,
    /// fact, execution state, or provenance node changes.
    pub(in crate::surface::proof) fn at_source_tactic(&self, index: usize) -> Self {
        if index != usize::MAX {
            crate::surface::note_ambient_source_tactic(self.context.claim_label(), index);
        }
        if self.site.addresses_source_tactic(index) {
            return self.clone();
        }
        Self {
            site: self.site.at_source_tactic(index),
            ..self.clone()
        }
    }

    /// The same proof, attributing its next step to `site`: a position a
    /// linear script runner computed for the written tactic it is about to
    /// check, or one a phase driver restores. Diagnostic addressing only,
    /// like [`Self::at_source_tactic`].
    pub(in crate::surface::proof) fn at_site(&self, site: &ProofStepSite) -> Self {
        Self {
            site: site.clone(),
            ..self.clone()
        }
    }

    /// The same fixed-state proof carrying `capture`, the recorder for a
    /// selected expansion target written inside a `have` body that this
    /// phase checks. The caller installs it only for the recorder's own
    /// proof site. Presentation metadata only: no check changes.
    pub(in crate::surface::proof) fn with_nested_tactic_capture(
        self,
        capture: Option<Arc<NestedTacticCapture>>,
    ) -> Self {
        let Some(capture) = capture else {
            return self;
        };
        let ProofContext::FixedState(context) = self.context.as_ref() else {
            return self;
        };
        let context = FixedStateProofContext {
            nested_tactic_capture: Some(capture),
            ..context.clone()
        };
        Self {
            context: Arc::new(ProofContext::FixedState(context)),
            ..self
        }
    }

    /// Starts recording this written tactic's checked delta when `click
    /// expand` selected it inside a `have` body: the proof carries the
    /// selected site's recorder and this step's source path is the selected
    /// one. Costs nothing unless an expansion installed a recorder.
    pub(in crate::surface::proof) fn begin_nested_tactic_capture(
        &self,
    ) -> Option<NestedTacticCaptureGuard<'a>> {
        let capture = match self.context.as_ref() {
            ProofContext::Execution(context) => {
                let capture = context.constants.nested_tactic_capture.as_ref()?;
                if context.constants.proof_site.as_ref() != Some(&capture.site) {
                    return None;
                }
                capture
            }
            // A fixed-state phase carries a recorder only when its driver
            // matched the recorder's site (see
            // `Self::with_nested_tactic_capture`).
            ProofContext::FixedState(context) => context.nested_tactic_capture.as_ref()?,
            ProofContext::Pure(_) => return None,
        };
        let capture = capture.at_path(&self.site.written_source_tactic_path()?)?;
        if !capture.try_begin() {
            return None;
        }
        Some(NestedTacticCaptureGuard {
            capture: capture.clone(),
            checkpoint: self.checkpoint(),
            finished: false,
        })
    }

    #[cfg(test)]
    fn fact_lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.facts().lookup_comparisons(fact)
    }
}

/// One claimed occurrence of a selected nested expansion target. Finishing
/// records the steps checked since the tactic began; dropping it without
/// finishing (the tactic failed or was abandoned by its caller) releases the
/// recorder with nothing recorded.
pub(in crate::surface::proof) struct NestedTacticCaptureGuard<'a> {
    capture: Arc<NestedTacticCapture>,
    checkpoint: ProofCheckpoint<'a>,
    finished: bool,
}

impl<'a> NestedTacticCaptureGuard<'a> {
    pub(in crate::surface::proof) fn finish(mut self, after: &Proof<'a>) {
        let occurrence = after
            .certificate_after_node(Some(&self.checkpoint.node))
            .map(|certificate| certificate.to_proof_tactics())
            .map_err(|error| error.raw_summary().to_string());
        self.capture.finish(occurrence);
        self.finished = true;
    }
}

impl Drop for NestedTacticCaptureGuard<'_> {
    fn drop(&mut self) {
        if !self.finished {
            self.capture.abandon();
        }
    }
}

/// The source-level form of one proof step, for diagnostics that point at a
/// line the user wrote.
fn proof_step_source_name(step: &ProofStep) -> &'static str {
    match step {
        ProofStep::Match { .. } => "match",
        ProofStep::Both { .. } => "both",
        ProofStep::Known => "known()",
        ProofStep::Normalize | ProofStep::NormalizeUsing(_) => "normalize()",
        ProofStep::ArithmeticUsing(_) => "solve() using",
        ProofStep::Preserve(_) => "preserve",
        ProofStep::ArithmeticCertificate(_) => "arithmetic_certificate",
        ProofStep::Intro | ProofStep::IntroAs(_) => "intro()",
        ProofStep::Enumerate => "enumerate()",
        ProofStep::Step
        | ProofStep::StepBind(_)
        | ProofStep::StepContract(_)
        | ProofStep::StepCall(_)
        | ProofStep::StepProved { .. } => "step",
        ProofStep::UserTactic(_) => "tactic application",
        ProofStep::ApplyTheoremUsing { .. } => "apply",
        ProofStep::ApplyInductionUsing { .. } => "apply",
        ProofStep::Induct { .. } => "induct",
        ProofStep::StructuralInduct { .. } => "induct",
        ProofStep::TransportUsing { .. } => "transport",
        ProofStep::InstantiateUsing { .. } => "instantiate",
        ProofStep::Have { .. } => "have",
        ProofStep::Open { .. } => "open",
        ProofStep::If { .. } => "if",
        ProofStep::Cases { .. } => "cases",
        ProofStep::Branch { .. } => "branch",
        ProofStep::CallOutcomes { .. } => "outcomes",
        ProofStep::Loop(_) => "loop",
        ProofStep::Rewrite(_) => "rewrite",
        ProofStep::Extract(_) => "extract",
        ProofStep::Contradiction(_) => "contradiction",
        ProofStep::Witness(_) => "witness",
        ProofStep::LetSatisfy(_) => "obtain",
        ProofStep::Choose(_) => "choose",
        ProofStep::UnfoldPredicate(_)
        | ProofStep::UnfoldFunction(_)
        | ProofStep::PeelFunction { .. }
        | ProofStep::UnfoldResource(_)
        | ProofStep::UnfoldWitnesses { .. } => "unfold",
        ProofStep::FoldResource(_) => "fold",
        ProofStep::ConstructResource(_) => "construct",
        ProofStep::ObserveResource(_) => "observe",
        ProofStep::Iterated(tactic) => tactic.name(),
        ProofStep::CloseInvariantsBy(_) => "close_invariants() by",
        ProofStep::Mark(_) => "mark",
    }
}

mod construction;
mod match_cases;
pub(in crate::surface::proof) use match_cases::ExecutionMatchPlan;
pub(in crate::surface::proof) use match_cases::PureMatchPlan;
mod execution_entry;
mod execution_joins;
pub(in crate::surface::proof) use execution_joins::StepUntilTarget;
mod execution_statements;
pub(in crate::surface::proof) use execution_statements::implicit_solve_disabled;
pub use execution_statements::without_implicit_solve;
mod fact_index;
mod fixed_state_steps;
mod outcomes_and_focus;
mod provenance;
pub(in crate::surface::proof) use provenance::ProofCheckpoint;
pub(in crate::surface::proof) use provenance::ProofStepSite;
use provenance::{ProofNode, ProofStepBlock, ProofStepOrigin};
mod resource_steps;
mod scope;
mod splits_and_scopes;
mod step_application;
mod trace_surface;

#[cfg(test)]
mod tests;

pub(in crate::surface::proof) use fact_index::collect_surface_conjunct_leaves;
pub(in crate::surface::proof) use outcomes_and_focus::frontier_premise_anchor;

impl ExecutionProofPresentation {
    pub(in crate::surface::proof) fn record_generated_load_bindings(
        &mut self,
        incoming: &[crate::kernel::GeneratedLoadBinding],
    ) {
        if incoming.is_empty() {
            return;
        }
        let mut by_variable = self.generated_load_bindings.clone();
        for binding in incoming {
            let variable = match binding {
                crate::kernel::GeneratedLoadBinding::Exact { variable, .. }
                | crate::kernel::GeneratedLoadBinding::Ambiguous { variable } => *variable,
            };
            let merged = match by_variable.get(&variable) {
                Some(crate::kernel::GeneratedLoadBinding::Ambiguous { .. }) => continue,
                Some(crate::kernel::GeneratedLoadBinding::Exact {
                    retained_state,
                    pointer,
                    load,
                    ..
                }) => match binding {
                    crate::kernel::GeneratedLoadBinding::Exact {
                        retained_state: next_state,
                        pointer: next_pointer,
                        load: next_load,
                        ..
                    } if retained_state == next_state
                        && pointer == next_pointer
                        && load == next_load =>
                    {
                        continue;
                    }
                    _ => crate::kernel::GeneratedLoadBinding::Ambiguous { variable },
                },
                None => binding.clone(),
            };
            by_variable = by_variable.with_inserted(variable, merged);
            self.generated_load_binding_events.push(binding.clone());
        }
        self.generated_load_bindings = by_variable;
    }

    /// Record exact source observations without consulting facts or a source
    /// registry.  Repeating the complete event is idempotent; changing either
    /// its source identity or exact producer binding permanently tombstones
    /// the variable as ambiguous.
    pub(in crate::surface::proof) fn record_generated_load_source_events(
        &mut self,
        incoming: &[crate::kernel::GeneratedLoadSourceEvent],
    ) {
        record_generated_load_source_events(
            &mut self.generated_load_source_resolutions,
            &mut self.generated_load_source_events,
            incoming,
        );
    }

    pub(in crate::surface::proof) fn defer_post_execution(
        &mut self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
        lexical_bindings: Option<PersistentMap<String, ContractExpression>>,
    ) {
        self.post_execution_tactics
            .push(DeferredPostExecutionTactic {
                lexical_bindings,
                tactic_index,
                source_index,
                tactic,
            });
    }
}

fn record_generated_load_source_events(
    resolutions: &mut PersistentMap<
        crate::kernel::Variable,
        crate::kernel::GeneratedLoadSourceResolution,
    >,
    events: &mut PersistentSequence<crate::kernel::GeneratedLoadSourceEvent>,
    incoming: &[crate::kernel::GeneratedLoadSourceEvent],
) {
    if incoming.is_empty() {
        return;
    }
    let mut by_variable = resolutions.clone();
    for event in incoming {
        let variable = event.variable();
        let merged = match by_variable.get(&variable) {
            Some(crate::kernel::GeneratedLoadSourceResolution::Ambiguous { .. }) => continue,
            Some(crate::kernel::GeneratedLoadSourceResolution::Unique(_))
                if matches!(
                    event.binding(),
                    crate::kernel::GeneratedLoadBinding::Ambiguous { .. }
                ) =>
            {
                crate::kernel::GeneratedLoadSourceResolution::Ambiguous { variable }
            }
            Some(crate::kernel::GeneratedLoadSourceResolution::Unique(existing))
                if existing == event =>
            {
                continue;
            }
            Some(crate::kernel::GeneratedLoadSourceResolution::Unique(_)) | None => {
                if by_variable.get(&variable).is_some() {
                    crate::kernel::GeneratedLoadSourceResolution::Ambiguous { variable }
                } else {
                    match event.binding() {
                        crate::kernel::GeneratedLoadBinding::Exact { .. } => {
                            crate::kernel::GeneratedLoadSourceResolution::Unique(event.clone())
                        }
                        crate::kernel::GeneratedLoadBinding::Ambiguous { .. } => {
                            crate::kernel::GeneratedLoadSourceResolution::Ambiguous { variable }
                        }
                    }
                }
            }
        };
        by_variable = by_variable.with_inserted(variable, merged);
        events.push(event.clone());
    }
    *resolutions = by_variable;
}

#[cfg(test)]
pub(in crate::surface) use outcomes_and_focus::take_outcome_fact_reads;

#[cfg(test)]
pub(in crate::surface) fn take_terminal_publication_visits() -> (usize, usize) {
    TERMINAL_PUBLICATION_VISITS.with(|counts| counts.replace((0, 0)))
}

/// Path facts terminal joins merged into fresh streams while republishing
/// their arms' paths, since the last call.
#[cfg(test)]
pub(in crate::surface) fn take_terminal_join_materialized_facts() -> usize {
    TERMINAL_JOIN_MATERIALIZED_FACTS.with(|count| count.replace(0))
}

#[cfg(test)]
mod authority_control_tests;

#[path = "driver/state.rs"]
mod driver;
