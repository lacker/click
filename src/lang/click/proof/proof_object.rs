use super::pure_theorems::PureTheoremContext;
use super::*;
use crate::kernel::proof::{
    BranchId, CheckedFrameAuthority, EffectGoalSelection, ExecutionUpdateError, FrontierObligation,
    FrontierSplitError, FunctionOutcomeObligation, OutcomeProofCore,
    OutcomeProofState as KernelOutcomeProofState, ProofBranch, ProofBranchState,
    ProofExecutionState as KernelProofExecutionState, ProofFacts, ProofFocusError, ProofJoinError,
    ProofObject as KernelProofObject, ProofObligation as KernelBranchObligation,
    ProofState as KernelProofState, PropositionAssumptionContext, PropositionCloseError,
    PropositionIntroduction, PropositionObligation as KernelPropositionObligation,
    PropositionSplitError, SplitId,
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
    static SOURCE_CERTIFICATE_CHECKS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static EXPLICIT_LINEAR_FALLBACKS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static EXECUTION_CONTEXT_EXPORTS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static COLLECTED_EXECUTION_CONTEXT_EXPORT_LABELS: std::cell::RefCell<Option<Vec<String>>> = const {
        std::cell::RefCell::new(None)
    };
    static CHECKED_EXPANDED_EXECUTION_IFS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static SMART_LOOP_EFFECT_FRAME_CANDIDATES: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
    static FINALIZATION_VIEW_CONSTRUCTIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
pub(in crate::lang::click) fn count_checked_execution_interface_joins<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = CHECKED_EXECUTION_INTERFACE_JOINS.with(std::cell::Cell::get);
    let result = operation();
    let after = CHECKED_EXECUTION_INTERFACE_JOINS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn count_source_certificate_checks<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = SOURCE_CERTIFICATE_CHECKS.with(std::cell::Cell::get);
    let result = operation();
    let after = SOURCE_CERTIFICATE_CHECKS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn count_explicit_linear_fallbacks<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = EXPLICIT_LINEAR_FALLBACKS.with(std::cell::Cell::get);
    let result = operation();
    let after = EXPLICIT_LINEAR_FALLBACKS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click::proof) fn record_explicit_linear_fallback() {
    EXPLICIT_LINEAR_FALLBACKS.with(|fallbacks| fallbacks.set(fallbacks.get() + 1));
}

#[cfg(test)]
pub(in crate::lang::click) fn count_execution_context_exports<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = EXECUTION_CONTEXT_EXPORTS.with(std::cell::Cell::get);
    let result = operation();
    let after = EXECUTION_CONTEXT_EXPORTS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn count_smart_loop_effect_frame_candidates<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = SMART_LOOP_EFFECT_FRAME_CANDIDATES.with(std::cell::Cell::get);
    let result = operation();
    let after = SMART_LOOP_EFFECT_FRAME_CANDIDATES.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn count_finalization_view_constructions<R>(
    operation: impl FnOnce() -> R,
) -> (R, usize) {
    let before = FINALIZATION_VIEW_CONSTRUCTIONS.with(std::cell::Cell::get);
    let result = operation();
    let after = FINALIZATION_VIEW_CONSTRUCTIONS.with(std::cell::Cell::get);
    (result, after - before)
}

#[cfg(test)]
pub(in crate::lang::click) fn collect_execution_context_export_labels<R>(
    operation: impl FnOnce() -> R,
) -> (R, Vec<String>) {
    COLLECTED_EXECUTION_CONTEXT_EXPORT_LABELS.with(|labels| {
        assert!(
            labels.borrow().is_none(),
            "execution-export label collectors cannot nest"
        );
        *labels.borrow_mut() = Some(Vec::new());
    });
    let result = operation();
    let labels = COLLECTED_EXECUTION_CONTEXT_EXPORT_LABELS.with(|labels| {
        labels
            .borrow_mut()
            .take()
            .expect("the active execution-export label collector was retained")
    });
    (result, labels)
}

#[cfg(test)]
pub(in crate::lang::click) fn count_checked_expanded_execution_ifs<R>(
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
    pub(in crate::lang::click::proof) context: Arc<ProofContext<'a>>,
    state: KernelProofHandle,
    node: Arc<ProofNode>,
}

/// Feasible arms of one checked C `if` frontier.
///
/// Entering the container performs the audited condition transition and C
/// frontier movement once. Arm bodies then extend the retained `Proof`
/// descendants; a join owns the corresponding structured certificate node.
#[derive(Clone)]

/// Bookkeeping for one in-`Proof` execution branch split: the split
/// identity and marker its joins verify, each feasible arm's recorded goal
/// id, condition theorem, and split-time fact base (the ancestor for
/// `introduced_since`), and the shared continuation data. This is a record
/// the audited joins check — never semantic authority.
pub(super) struct ExecutionSplit<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    arm_branches: [Option<BranchId>; 2],
    condition_theorems: [Option<Theorem>; 2],
    base_facts: [Option<ProofFacts>; 2],
    base_executions: [Option<Arc<ExecutionProofState>>; 2],
    path_facts: [Option<Vec<Proposition>>; 2],
    parent_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    statement_index: usize,
    continuation_index: usize,
    continuation_remaining: Option<Arc<CStatement>>,
    execution_start_state: CState,
}

/// Bookkeeping for an exhaustive proof-level case split over one execution
/// frontier. The `if` is logical rather than a C branch.
pub(super) struct ExecutionProofCaseSplit<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    arm_branches: [BranchId; 2],
    surface_condition: ClickProposition,
    base_facts: [ProofFacts; 2],
    base_executions: [Arc<ExecutionProofState>; 2],
    path_facts: [Vec<Proposition>; 2],
    common_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    execution_start_state: CState,
}

/// Bookkeeping for one logical `cases` split over an execution frontier.
/// Unlike an execution `if`, this split introduces the two exact disjuncts
/// from an already-available proposition and does not write a C-path choice
/// into the execution state.
pub(super) struct ExecutionLogicalCasesSplit<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    arm_branches: [BranchId; 2],
    path_facts: [Vec<Proposition>; 2],
}

/// One checked branch arm's contribution to a checked execution join: the
/// arm's structured certificate, final facts and execution snapshot,
/// recorded condition theorem, and the introduction deltas the merge
/// re-applies on the shared continuation. The container join and the
/// in-`Proof` sibling join both reduce their arms to this view, so the
/// merge law has one implementation.
struct CheckedExecutionJoinArm<'v> {
    certificate: ProofCertificate,
    facts: &'v ProofFacts,
    execution: &'v ExecutionProofState,
    condition_theorem: Option<&'v Theorem>,
    introduced_facts: Vec<Proposition>,
    introduced_effect_facts: Vec<ExecutionPureFact>,
    introduced_prerequisites: Vec<Proposition>,
    introduced_derivations: Vec<Theorem>,
    introduced_unfolds: Vec<String>,
    /// Frontier-local loops the arm proved inside its region. They are
    /// checked function-proof state, so a join carries them like unfolds.
    introduced_loop_clauses: Vec<StructuralClause>,
    introduced_loop_rules: Vec<CVerifiedLoopRule>,
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
}

impl<'a> ExecutionSplit<'a> {
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
    /// when the shared continuation is derivable and both arm snapshots
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

/// Bookkeeping for one in-`Proof` terminal-outcome partition split: the
/// marker and recorded arm ids its join verifies, the partition condition
/// and the effect selection both arms must close, the parent context the
/// join resumes, and each arm's entry fact delta. This is a record the
/// audited join checks — never semantic authority.
pub(super) struct OutcomeSplit<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    arm_branches: [BranchId; 2],
    condition: ClickProposition,
    expected_effects: Vec<usize>,
    path_facts: [Vec<Proposition>; 2],
    parent_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    root_post_execution_count: usize,
}

/// The audited branch-entry result shared by the execution container and
/// the in-`Proof` sibling split: source structure plus each feasible arm's
/// checked facts, snapshot, path-fact delta, and condition theorem.
struct PreparedExecutionBranch {
    statement_index: usize,
    continuation_index: usize,
    continuation_remaining: Option<Arc<CStatement>>,
    execution_start_state: CState,
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
    remaining: Arc<CStatement>,
    next_statement_index: usize,
    continuations: PersistentSequence<ProofExecutionContinuation>,
}

/// Derives the exact nonterminal frontier reached after a checked C branch
/// completes, from the branch root's execution and recorded continuation
/// data. See [`ExecutionBranchJoinContinuation`].
fn derive_execution_join_continuation(
    root_execution: &ExecutionProofState,
    continuation_remaining: &Option<Arc<CStatement>>,
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
}

#[derive(Clone)]
enum ProofScopeStructure {
    Have {
        proposition: ClickProposition,
        kernel: Proposition,
        /// The explicit script proving this `have`, when the source gave
        /// one. The join carries standard-theorem authority selected by an
        /// explicit `apply using` at function entry into the enclosing
        /// execution frontier, as the shared mid-execution law does.
        script: Option<Vec<ProofTactic>>,
    },
    Open {
        resource: ResourceClause,
        source_index: usize,
        preserve_exposed_body: bool,
    },
}

pub(in crate::lang::click::proof) fn explicit_linear_step(
    tactic: &ProofTactic,
) -> Option<ProofStep> {
    match tactic {
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Some(ProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::UnfoldPredicate(name) => Some(ProofStep::UnfoldPredicate(name.clone())),
        ProofTactic::Witness(witness) => Some(ProofStep::Witness(witness.clone())),
        ProofTactic::Choose(choice) => Some(ProofStep::Choose(choice.clone())),
        ProofTactic::Assumption => Some(ProofStep::Assumption),
        ProofTactic::Extract(proposition) => Some(ProofStep::Extract(proposition.clone())),
        ProofTactic::Normalize => Some(ProofStep::Normalize),
        ProofTactic::Intro => Some(ProofStep::Intro),
        ProofTactic::Split => Some(ProofStep::Split),
        ProofTactic::Left => Some(ProofStep::Left),
        ProofTactic::Right => Some(ProofStep::Right),
        ProofTactic::Enumerate => Some(ProofStep::Enumerate),
        ProofTactic::Contradiction(proposition) => {
            Some(ProofStep::Contradiction(proposition.clone()))
        }
        ProofTactic::Rewrite(proposition) => Some(ProofStep::Rewrite(proposition.clone())),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Some(ProofStep::TransportUsing {
            source: source.clone(),
            target: target.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::InstantiateUsing {
            quantified,
            argument,
            premises,
        } => Some(ProofStep::InstantiateUsing {
            quantified: quantified.clone(),
            argument: argument.clone(),
            premises: premises.clone(),
        }),
        _ => None,
    }
}

fn source_proof_contains_linear_search(proof: &SourceProof) -> bool {
    match proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        SourceProof::Script(tactics) => script_contains_linear_search(tactics),
        SourceProof::Tactic(SmartTactic::Frame) => false,
    }
}

/// Collects only source-local C names mentioned by one candidate statement.
/// Smart statement selection uses these names as keys into the persistent
/// Surface-fact index; it never scans the ambient proposition set.
fn collect_expression_variable_names(expression: &CExpression, names: &mut BTreeSet<String>) {
    match expression {
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::Value(_) => {}
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_expression_variable_names(pointer, names)
        }
        CExpression::AddressOf(inner) | CExpression::Not(inner) | CExpression::Load(inner) => {
            collect_expression_variable_names(inner, names)
        }
        CExpression::TypedLoad { pointer, .. } => collect_expression_variable_names(pointer, names),
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_expression_variable_names(left, names);
            collect_expression_variable_names(right, names);
        }
        CExpression::BitwiseNot(inner) => collect_expression_variable_names(inner, names),
    }
}

fn collect_statement_variable_names(statement: &CStatement, names: &mut BTreeSet<String>) {
    match statement {
        CStatement::Skip | CStatement::Declare { .. } => {}
        CStatement::Assign { name, expression } => {
            names.insert(name.clone());
            collect_expression_variable_names(expression, names);
        }
        CStatement::Return(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        }
        | CStatement::HeapAllocate {
            bytes: expression, ..
        }
        | CStatement::HeapFree {
            pointer: expression,
        } => collect_expression_variable_names(expression, names),
        CStatement::CallAssign {
            target, arguments, ..
        } => {
            names.insert(target.clone());
            for argument in arguments {
                collect_expression_variable_names(argument, names);
            }
        }
        CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_expression_variable_names(argument, names);
            }
        }
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            collect_expression_variable_names(pointer, names);
            collect_expression_variable_names(value, names);
        }
        // The execution cursor normally splits sequences before selection.
        // If a composite statement reaches this helper, only its immediate
        // operation may influence the next checked transition; later source
        // must not widen one smart step's dependency query.
        CStatement::Seq(first, _) => {
            collect_statement_variable_names(first, names);
        }
        CStatement::If { condition, .. } => {
            collect_expression_variable_names(condition, names);
        }
        CStatement::While { condition, .. } => {
            collect_expression_variable_names(condition, names);
        }
    }
}

pub(super) fn script_contains_linear_search(tactics: &[ProofTactic]) -> bool {
    tactics.iter().any(|tactic| match tactic {
        ProofTactic::ApplyTheorem(_) | ProofTactic::Simp | ProofTactic::SimpUsing(_) => true,
        ProofTactic::Have(have) => source_proof_contains_linear_search(&have.proof),
        ProofTactic::If(proof_if) => {
            script_contains_linear_search(&proof_if.then_tactics)
                || script_contains_linear_search(&proof_if.else_tactics)
        }
        ProofTactic::Cases(proof_cases) => {
            script_contains_linear_search(&proof_cases.left_tactics)
                || script_contains_linear_search(&proof_cases.right_tactics)
        }
        _ => false,
    })
}

fn branch_arm_is_supported(tactics: &[ProofTactic]) -> bool {
    linear_script_is_supported(tactics)
}

pub(in crate::lang::click::proof) fn source_proof_is_supported(proof: &SourceProof) -> bool {
    match proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        SourceProof::Script(tactics) => linear_script_is_supported(tactics),
        SourceProof::Tactic(SmartTactic::Frame) => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ContextualFrameHavePlan {
    proposition: ClickProposition,
    tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ContextualFrameLeafPlan {
    haves: Vec<ContextualFrameHavePlan>,
    premises: Vec<ClickProposition>,
}

impl ContextualFrameLeafPlan {
    fn from_surface_tactics(mut tactics: Vec<ProofTactic>) -> Result<Self, String> {
        let Some(ProofTactic::FrameUsing {
            region: None,
            premises,
        }) = tactics.pop()
        else {
            return Err("contextual frame path did not end in `frame using`".to_string());
        };
        let haves = tactics
            .into_iter()
            .map(|tactic| {
                let ProofTactic::Have(ProofHave { proposition, proof }) = tactic else {
                    return Err(
                        "contextual frame path contained an operation other than `have` before its frame"
                            .to_string(),
                    );
                };
                let SourceProof::Script(tactics) = proof else {
                    return Err(
                        "contextual frame `have` did not lower to explicit Surface operations"
                            .to_string(),
                    );
                };
                Ok(ContextualFrameHavePlan {
                    proposition,
                    tactics,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self { haves, premises })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ContextualFramePlan {
    Leaf(ContextualFrameLeafPlan),
    If {
        condition: ClickProposition,
        then_plan: Box<Self>,
        else_plan: Box<Self>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ContextualFrameSkeleton {
    Leaf,
    If {
        condition: ClickProposition,
        then_skeleton: Box<Self>,
        else_skeleton: Box<Self>,
    },
}

impl ContextualFrameSkeleton {
    fn from_steps(steps: &[ProofStep]) -> Self {
        let Some((condition, then_proof, else_proof)) =
            steps.iter().rev().find_map(|step| match step {
                ProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                } => Some((condition, then_proof, else_proof)),
                _ => None,
            })
        else {
            return Self::Leaf;
        };
        Self::If {
            condition: condition.clone(),
            then_skeleton: Box::new(Self::from_steps(then_proof.steps())),
            else_skeleton: Box::new(Self::from_steps(else_proof.steps())),
        }
    }

    fn collect_conditions(&self, conditions: &mut Vec<ClickProposition>) {
        let Self::If {
            condition,
            then_skeleton,
            else_skeleton,
        } = self
        else {
            return;
        };
        if !conditions.contains(condition) {
            conditions.push(condition.clone());
        }
        then_skeleton.collect_conditions(conditions);
        else_skeleton.collect_conditions(conditions);
    }

    fn fill(
        self,
        leaves: &[ContextualFrameLeafPlan],
        next: &mut usize,
    ) -> Result<ContextualFramePlan, String> {
        match self {
            Self::Leaf => {
                let Some(leaf) = leaves.get(*next) else {
                    return Err(format!(
                        "surface/frame path coverage diverged at p{}: the Proof has more leaves than the frame plan",
                        *next
                    ));
                };
                *next += 1;
                Ok(ContextualFramePlan::Leaf(leaf.clone()))
            }
            Self::If {
                condition,
                then_skeleton,
                else_skeleton,
            } => Ok(ContextualFramePlan::If {
                condition,
                then_plan: Box::new(then_skeleton.fill(leaves, next)?),
                else_plan: Box::new(else_skeleton.fill(leaves, next)?),
            }),
        }
    }
}

fn contextual_frame_plan(
    skeleton: ContextualFrameSkeleton,
    path_tactics: Vec<Vec<ProofTactic>>,
    path_independent_only: bool,
) -> Result<Option<ContextualFramePlan>, String> {
    if path_tactics.is_empty() {
        return Ok(None);
    }
    let leaves = path_tactics
        .into_iter()
        .map(ContextualFrameLeafPlan::from_surface_tactics)
        .collect::<Result<Vec<_>, _>>()?;
    if leaves.iter().all(|leaf| leaf == &leaves[0]) {
        return Ok(Some(ContextualFramePlan::Leaf(leaves[0].clone())));
    }
    if path_independent_only {
        return Ok(None);
    }
    let mut next = 0;
    let plan = skeleton.fill(&leaves, &mut next)?;
    if next != leaves.len() {
        return Err(format!(
            "surface/frame path coverage diverged at p{next}: the Proof has {next} leaves but the frame plan has {}",
            leaves.len()
        ));
    }
    Ok(Some(plan))
}

fn reverse_surface_comparison(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let operator = match operator {
                ComparisonOperator::Equal => ComparisonOperator::Equal,
                ComparisonOperator::NotEqual => ComparisonOperator::NotEqual,
                ComparisonOperator::LessThan => ComparisonOperator::GreaterThan,
                ComparisonOperator::LessEqual => ComparisonOperator::GreaterEqual,
                ComparisonOperator::GreaterThan => ComparisonOperator::LessThan,
                ComparisonOperator::GreaterEqual => ComparisonOperator::LessEqual,
            };
            Some(ClickProposition::Comparison {
                left: right.clone(),
                operator,
                right: left.clone(),
            })
        }
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(reverse_surface_comparison(proposition)?),
        }),
        ClickProposition::Not(body) => Some(ClickProposition::Not(Box::new(
            reverse_surface_comparison(body)?,
        ))),
        _ => None,
    }
}

pub(in crate::lang::click::proof) fn linear_script_is_supported(tactics: &[ProofTactic]) -> bool {
    !tactics.is_empty()
        && tactics
            .iter()
            .enumerate()
            .all(|(index, tactic)| match tactic {
                ProofTactic::ApplyTheorem(_) => true,
                ProofTactic::Simp => index + 1 == tactics.len(),
                ProofTactic::SimpUsing(_) => index + 1 == tactics.len(),
                ProofTactic::Have(have) => source_proof_is_supported(&have.proof),
                ProofTactic::If(proof_if) => {
                    index + 1 == tactics.len()
                        && branch_arm_is_supported(&proof_if.then_tactics)
                        && branch_arm_is_supported(&proof_if.else_tactics)
                }
                ProofTactic::Cases(proof_cases) => {
                    index + 1 == tactics.len()
                        && branch_arm_is_supported(&proof_cases.left_tactics)
                        && branch_arm_is_supported(&proof_cases.right_tactics)
                }
                tactic => explicit_linear_step(tactic).is_some(),
            })
}

type ProofState = KernelProofState<ProofLocals, Obligation, ExecutionProofState>;

/// Proof-local surface names introduced by checked refinements such as
/// `choose`. The persistent map makes forks and one local binding logarithmic;
/// the counter is branch-local scalar freshness state.
#[derive(Clone)]
struct ProofLocals {
    values: PersistentMap<String, ContractExpression>,
    next_choice_variable: u64,
}

impl Default for ProofLocals {
    fn default() -> Self {
        Self {
            values: PersistentMap::default(),
            next_choice_variable: 3_000_000,
        }
    }
}

/// Execution data whose unchanged pieces can be shared by checked `Proof`
/// successors. Pure facts live in `ProofState::facts`; this contains only the
/// frontier state, certificate-construction metadata, and persistent branch provenance.
#[derive(Clone)]
pub(in crate::lang::click::proof) struct ExecutionProofPresentation {
    /// The immutable states recorded under program points or proof marks,
    /// which `at(selector, ...)` premises resolve against.
    pub(in crate::lang::click::proof) recorded_snapshots: RecordedSnapshots,
    /// The surface spellings this path has lowered, paired with their
    /// kernel propositions, so premises can be written as the source wrote
    /// them.
    pub(in crate::lang::click::proof) surface_propositions: SurfacePropositionMap,
    /// Case assumptions introduced on this path by proof-level splits.
    pub(in crate::lang::click::proof) case_assumptions: PersistentSequence<CaseAssumption>,
    /// Frontier-local loop clauses, paired with the kernel-owned verified
    /// rules and migrated across joins as arm deltas.
    pub(in crate::lang::click::proof) frontier_loop_clauses: PersistentSequence<StructuralClause>,
    /// Outcome tactics deferred during execution, applied in order at
    /// finalization; joins carry each arm's suffix.
    pub(in crate::lang::click::proof) post_execution_tactics:
        PersistentSequence<DeferredPostExecutionTactic>,
    /// The path's surface record: certificate-visible certificate facts, the
    /// premise anchor, and proof-level case choices.
    pub(in crate::lang::click::proof) surface_record: SurfaceRecord,
    /// Where the checked `close_invariants` tactic sat, so the invariant
    /// bundle check its caller performs after the check finishes can be
    /// timed against that tactic's own identity instead of going unattributed.
    ///
    /// `close_invariants` only records the intent during check; the kernel
    /// re-derivation that gives it meaning runs in
    /// `verify_one_loop_preservation_proof` once the whole certificate has
    /// checked. Without this the dominant cost of the loop-invariant bundle
    /// carries no class tag at all (`git history (profiler coverage, 2026-07-31)`).
    pub(in crate::lang::click::proof) invariant_closer_step: Option<InvariantCloserStep>,
    /// Where a smart region-level invariant closer was written. Like the
    /// explicit closer above, this is expansion and timing attribution only;
    /// the kernel-owned invariant-closure flag carries semantic authority.
    pub(in crate::lang::click::proof) region_simp: Option<(usize, usize)>,
    /// Semantic transition evidence recorded by planning so the surface step
    /// constructed for a statement move can consult the certified transition.
    /// It is deliberately separate from `ProofTactic` so internal execution
    /// artifacts cannot masquerade as proof steps.
    pub(in crate::lang::click::proof) planned_statement_transitions:
        SharedVec<PlannedStatementTransition>,
    /// Where a source tactic's expansion is being captured on this path.
    pub(in crate::lang::click::proof) expansion: ExpansionCursor,
    pub(in crate::lang::click::proof) branch_path: PersistentSequence<String>,
    /// Kernel facts whose checked C-branch Surface spellings must survive a
    /// join for extraction and explicit historical premises.
    pub(in crate::lang::click::proof) branch_surface_facts: PersistentOrderedSet<Proposition>,
    /// Decisions on the currently focused branch execution lineage. Forks append
    /// one entry in constant time.
    branch_decisions: PersistentSequence<ExecutionBranchDecision>,
    /// Path-local provenance aligned with terminal execution candidates.
    /// Keeping each outcome's lineage, Surface lowerings, and recorded-snapshot
    /// snapshots in one record makes their correspondence structural rather
    /// than an invariant across parallel vectors. The record is output-sized
    /// Proof provenance; its persistent roots do not copy semantic state.
    outcome_provenance: Arc<Vec<OutcomeProvenance>>,
}

pub(in crate::lang::click::proof) type ExecutionProofState =
    KernelProofExecutionState<ExecutionProofPresentation>;

impl ExecutionProofState {
    fn provenance_for_outcome(&self, path_index: usize) -> OutcomeProvenance {
        self.presentation
            .outcome_provenance
            .get(path_index)
            .cloned()
            .unwrap_or_else(|| OutcomeProvenance {
                branch_decisions: self.presentation.branch_decisions.clone(),
                surface_propositions: self.presentation.surface_propositions.clone(),
                recorded_snapshots: self.presentation.recorded_snapshots.clone(),
            })
    }

    /// The read-only execution data lowering and fixed-state proofs consult.
    pub(in crate::lang::click::proof) fn view<'s>(
        &'s self,
        context: &'s ExecutionProofContext<'_>,
    ) -> ExecutionView<'s> {
        ExecutionView::new(
            &self.core.frontier,
            &self.core.effect_facts,
            &self.presentation.recorded_snapshots,
            &self.presentation.surface_propositions,
            context.constants.function_entry_state.as_ref(),
        )
    }

    /// The execution state at a proof's entry: the frontier's C state and
    /// effect facts with no branch provenance yet.
    pub(in crate::lang::click::proof) fn at_entry(
        state: CState,
        frontier: ExecutionFrontier,
        recorded_snapshots: RecordedSnapshots,
        surface_propositions: SurfacePropositionMap,
        branch_path: PersistentSequence<String>,
    ) -> Self {
        Self::new(
            ExecutionProofCore::at_entry(state, frontier),
            ExecutionProofPresentation {
                recorded_snapshots,
                surface_propositions,
                case_assumptions: PersistentSequence::default(),
                frontier_loop_clauses: PersistentSequence::default(),
                post_execution_tactics: PersistentSequence::default(),
                surface_record: SurfaceRecord::default(),
                invariant_closer_step: Default::default(),
                region_simp: None,
                planned_statement_transitions: Default::default(),
                expansion: ExpansionCursor::default(),
                branch_path,
                branch_surface_facts: PersistentOrderedSet::default(),
                branch_decisions: PersistentSequence::default(),
                outcome_provenance: Arc::new(Vec::new()),
            },
        )
    }
}

#[derive(Clone)]
struct ExecutionBranchDecision {
    condition: ClickProposition,
    value: bool,
    /// A proof-level case split (`if P { ... } else { ... }` in the proof),
    /// whose fact holds from function entry, as opposed to a C `branch`
    /// decision, which holds only at its statement.
    proof_case: bool,
}

/// Read-only terminal data borrowed from an execution `Proof` by claim
/// finalization. This view carries no transition methods and owns no semantic
/// state; the `Proof` remains alive as the sole authority while finalization
/// checks its typed outcome goals.
pub(super) struct ProofExecutionView<'p> {
    pub(super) state: &'p CState,
    pub(super) facts: Vec<Proposition>,
    pub(super) frontier: &'p ExecutionFrontier,
    pub(super) execution: &'p ExecutionProofState,
    pub(super) context: &'p ExecutionProofContext<'p>,
    pub(super) unfolded_predicates: &'p SharedVec<String>,
    pub(super) branch_path: &'p PersistentSequence<String>,
    outcome_provenance: &'p [OutcomeProvenance],
}

impl ProofExecutionView<'_> {
    /// The proof-level case decisions recorded on one outcome path, in
    /// decision order: each is a surface condition and the arm taken.
    pub(super) fn path_case_decisions(&self, path_index: usize) -> Vec<(ClickProposition, bool)> {
        self.outcome_provenance
            .get(path_index)
            .map(|provenance| {
                provenance
                    .branch_decisions
                    .iter()
                    .filter(|decision| decision.proof_case)
                    .map(|decision| (decision.condition.clone(), decision.value))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Selects the retained surface branch skeleton for one checked outcome.
    /// Decisions are Proof provenance recorded at the typed splits; expansion
    /// reads them without reconstructing semantic facts from the post-state.
    pub(super) fn surface_branch_path(
        &self,
        path_index: usize,
        tactics: &[ProofTactic],
    ) -> Option<Vec<bool>> {
        let mut decisions = self
            .outcome_provenance
            .get(path_index)?
            .branch_decisions
            .iter()
            .rev();
        let mut path = Vec::new();
        let mut current = tactics;
        loop {
            let Some(proof_if) = current.iter().rev().find_map(|tactic| match tactic {
                ProofTactic::If(proof_if) => Some(proof_if),
                _ => None,
            }) else {
                return Some(path);
            };
            let selected_then = decisions
                .find(|decision| decision.condition == proof_if.condition)?
                .value;
            path.push(selected_then);
            current = if selected_then {
                &proof_if.then_tactics
            } else {
                &proof_if.else_tactics
            };
        }
    }
}

#[derive(Clone)]
struct OutcomeProvenance {
    branch_decisions: PersistentSequence<ExecutionBranchDecision>,
    surface_propositions: SurfacePropositionMap,
    recorded_snapshots: RecordedSnapshots,
}

type Obligation = KernelBranchObligation<PropositionPresentation, Arc<OutcomeProofData>>;

type KernelProofHandle = KernelProofObject<ProofLocals, Obligation, ExecutionProofState>;
type PropositionObligation =
    KernelPropositionObligation<PropositionPresentation, Arc<OutcomeProofData>>;
type OutcomeObligation = FunctionOutcomeObligation<Arc<OutcomeProofData>>;

/// The fixed-state data a result-aware checker consumes, resolved from
/// either a fixed-state proof's borrowed context or a focused function-outcome
/// goal (see [`Proof::outcome_fixed_state_view`]).
/// Which effect-availability context an outcome-goal fixed-state operation
/// consumes; each migrated tactic matches its legacy drain input exactly.
#[derive(Clone, Copy)]
pub(in crate::lang::click::proof) enum OutcomeEffectContext {
    Path,
    Frontier,
}

#[derive(Clone, Copy)]
pub(in crate::lang::click::proof) struct FixedStateOperationView<'p> {
    pub(in crate::lang::click::proof) claim_label: &'p str,
    pub(in crate::lang::click::proof) tactic_index: usize,
    pub(in crate::lang::click::proof) effect_facts: &'p [ExecutionPureFact],
    pub(in crate::lang::click::proof) parameters: &'p [syntax::C0Parameter],
    pub(in crate::lang::click::proof) arguments: &'p [CExpression],
    pub(in crate::lang::click::proof) pre_state: &'p CState,
    pub(in crate::lang::click::proof) state: &'p CState,
    pub(in crate::lang::click::proof) result: Option<&'p CValue>,
    pub(in crate::lang::click::proof) recorded_snapshots: &'p RecordedSnapshots,
    pub(in crate::lang::click::proof) surface_propositions: &'p SurfacePropositionMap,
    pub(in crate::lang::click::proof) predicate_environment: &'p PredicateEnvironment,
    pub(in crate::lang::click::proof) click_function_environment: &'p ClickFunctionEnvironment,
    pub(in crate::lang::click::proof) theorem_environment: &'p TheoremEnvironment,
    pub(in crate::lang::click::proof) original_requirements: &'p [Requirement],
    pub(in crate::lang::click::proof) requirement_label_indices:
        Option<&'p BTreeMap<String, usize>>,
    pub(in crate::lang::click::proof) requirement_facts: &'p [Proposition],
}

impl<'p> FixedStateOperationView<'p> {
    fn from_fixed_state(context: &'p FixedStateProofContext<'_>) -> Self {
        Self {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: context.effect_facts,
            parameters: context.parameters,
            arguments: context.arguments,
            pre_state: context.pre_state,
            state: context.state,
            result: context.result,
            recorded_snapshots: context.recorded_snapshots,
            surface_propositions: context.surface_propositions,
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
            theorem_environment: context.theorem_environment,
            original_requirements: context.original_requirements,
            requirement_label_indices: context.requirement_label_indices,
            requirement_facts: context.requirement_facts,
        }
    }
}

/// One path-local function-outcome judgment: the checked return outcome of
/// one execution path awaiting its result-dependent continuations.
///
/// The goal owns the path's result value, post-outcome C state, and fact
/// context, and borrows the function-exit frontier's snapshot by identity
/// for lowering. Result and effect operations will consume these goals
/// directly instead of converting through a mutable execution-context adapter.
/// The result-aware data one function outcome supplies to fixed-state operations:
/// its checked return value, post-outcome state, recorded surface
/// lowerings, and effect-availability facts.
#[derive(Clone)]
pub(in crate::lang::click::proof) struct OutcomeProofPresentation {
    pub(in crate::lang::click::proof) surface_propositions: SurfacePropositionMap,
    pub(in crate::lang::click::proof) recorded_snapshots: RecordedSnapshots,
    /// The statement-entry anchor for premises naming a C local after it
    /// left scope, captured from the frontier at derivation.
    pub(in crate::lang::click::proof) premise_anchor: Option<ProgramPointRef>,
    /// The lowered function-requirement facts in declaration order, captured
    /// as the raw prefix of the drain's working set at derivation: `choose`
    /// selects its source by requirement index, which persistent
    /// deduplication would misalign.
    /// Original proposition requirements keyed by their checked entry fact.
    /// Typed outcome evidence uses this persistent index to recover an exact
    /// function-entry Surface premise without scanning unrelated facts.
    pub(in crate::lang::click::proof) requirement_surfaces:
        Arc<PersistentMap<Proposition, ClickProposition>>,
    branch_decisions: PersistentSequence<ExecutionBranchDecision>,
}

pub(in crate::lang::click::proof) type OutcomeProofData =
    KernelOutcomeProofState<OutcomeProofPresentation>;

type BranchState = ProofBranchState<ExecutionProofState>;
type OpenBranch = ProofBranch<Obligation, ExecutionProofState>;

/// One proposition judgment keeps its checked kernel meaning and, when the
/// judgment originated in Surface Click, the exact syntax needed to refine
/// structural goals. Both values belong to the same immutable Proof state;
/// smart search must not carry a second caller-owned description of its goal.
#[derive(Clone)]
pub(in crate::lang::click::proof) struct PropositionPresentation {
    pub(in crate::lang::click::proof) surface: Option<Arc<ClickProposition>>,
    /// Surface names introduced while refining this exact proposition goal.
    /// Universal binders are goal-local: sibling goals share the persistent
    /// map root at a split, then refine independently without leaking names.
    pub(in crate::lang::click::proof) surface_bindings: PersistentMap<String, ContractExpression>,
}

impl KernelPropositionObligation<PropositionPresentation, Arc<OutcomeProofData>> {
    fn kernel(&self) -> &Proposition {
        self.proposition()
    }
}

trait OpenBranchConstruction {
    fn proposition_in(state: BranchState, kernel: Proposition) -> Self;
    fn frontier(selection: EffectGoalSelection, state: BranchState) -> Self;
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
                },
            )),
            state,
        )
    }

    fn frontier(selection: EffectGoalSelection, state: BranchState) -> Self {
        Self::new(
            Obligation::Frontier(FrontierObligation::new(selection)),
            state,
        )
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
                },
                outcome,
            )),
            state,
        )
    }
}

/// An equality with an `old(...)` operand can use that entry expression's
/// reflexivity as an explicit transport source. Keep this selector
/// intentionally syntactic: the fixed-state checker remains the authority for
/// whether execution effects and result provenance permit the transport.
pub(in crate::lang::click::proof) fn old_reflexive_transport_source(
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
    let old = match (left, right) {
        (_, ContractExpression::Old(_)) => right,
        (ContractExpression::Old(_), _) => left,
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
            context: self.context.clone(),
            state,
            node: self.node.clone(),
        }
    }

    fn state(&self) -> &ProofState {
        self.state.state()
    }

    fn focused_branch_id(&self) -> BranchId {
        self.state.focused_branch()
    }

    /// The open branch addressed by this handle. Focus is only a cursor;
    /// sibling branches remain in the same immutable proof state.
    fn focused_branch(&self) -> Option<&OpenBranch> {
        self.state().open_branches.get(self.focused_branch_id())
    }

    fn focused_obligation(&self) -> Option<&Obligation> {
        Some(&self.focused_branch()?.obligation)
    }

    pub(in crate::lang::click::proof) fn proposition_obligation(
        &self,
    ) -> Option<&PropositionObligation> {
        match self.focused_obligation()? {
            Obligation::Proposition(goal) => Some(goal),
            _ => None,
        }
    }

    pub(in crate::lang::click::proof) fn local_binding(
        &self,
        name: &String,
    ) -> Option<&ContractExpression> {
        self.state().locals.values.get(name)
    }

    /// Whether the obligation this handle addresses has been discharged. On
    /// a single-goal proof this coincides with completion; inside a sibling
    /// split, only the focused branch obligation's discharge is an arm's success —
    /// the sibling legitimately remains open.
    pub(super) fn focused_discharged(&self) -> bool {
        self.state()
            .open_branches
            .get(self.focused_branch_id())
            .is_none()
    }

    /// The focused branch branch's path-local execution state, shared by identity
    /// with the frontier that created it.
    fn branch_execution(&self) -> Option<&Arc<ExecutionProofState>> {
        self.focused_branch()?.state.execution.as_ref()
    }

    /// The focused branch branch's path-local unfold delta.
    pub(in crate::lang::click::proof) fn focused_branch_unfolds(
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
    pub(in crate::lang::click::proof) fn facts(&self) -> &ProofFacts {
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
    ) -> OpenBranch {
        let outcome = match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => goal.outcome.clone(),
            Some(Obligation::FunctionOutcome(goal)) => Some(goal.data.clone()),
            _ => None,
        };
        let presentation = PropositionPresentation {
            surface: surface.map(Arc::new),
            surface_bindings: match self.focused_obligation() {
                Some(Obligation::Proposition(goal)) => goal.surface_bindings.clone(),
                _ => PersistentMap::default(),
            },
        };
        let obligation = match outcome {
            Some(outcome) => PropositionObligation::at_outcome(kernel, presentation, outcome),
            None => PropositionObligation::new(kernel, presentation),
        };
        OpenBranch::new(Obligation::Proposition(obligation), state)
    }

    /// The execution proof's per-proof context, when this is one.
    pub(in crate::lang::click::proof) fn execution_context(
        &self,
    ) -> Option<&ExecutionProofContext<'a>> {
        match self.context.as_ref() {
            ProofContext::Execution(context) => Some(context),
            _ => None,
        }
    }

    pub(in crate::lang::click::proof) fn execution(&self) -> Option<&ExecutionProofState> {
        self.branch_execution().map(Arc::as_ref)
    }

    #[cfg(test)]
    fn branches_next_id(&self) -> u64 {
        self.state().open_branches.next_id_for_test()
    }

    #[cfg(test)]
    fn outcome_result(&self) -> Option<&CValue> {
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

    pub(in crate::lang::click::proof) fn surface_goal(&self) -> Option<&ClickProposition> {
        match self.focused_obligation() {
            Some(Obligation::Proposition(goal)) => goal.surface.as_deref(),
            _ => None,
        }
    }

    /// Number of selected function-effect obligations represented by this
    /// frontier without materializing their clauses.
    #[cfg(test)]
    fn effect_goal_count(&self) -> usize {
        let Some(Obligation::Frontier(FrontierObligation { selection, .. })) =
            self.focused_obligation()
        else {
            return 0;
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return 0;
        };
        match *selection {
            EffectGoalSelection::None => 0,
            EffectGoalSelection::One(index) => {
                usize::from(index < context.function_block.effects().len())
            }
            EffectGoalSelection::All => context.function_block.effects().len(),
        }
    }

    /// Starts one externally selected proposition judgment from a
    /// fixed-state proof context without rebuilding its persistent facts.
    ///
    /// Grouped contract finalization owns several independent ensure goals;
    /// this audited root operation focuses one of them while sharing the
    /// checked outcome context. It is not a proof transition and therefore
    /// starts fresh provenance. A fixed-state descendant may have published
    /// checked `have` facts before another external obligation is selected;
    /// a proof that already owns a proposition goal cannot replace it.
    pub(super) fn focus_fixed_state_goal(&self, goal: Proposition) -> Result<Self, ClickError> {
        self.focus_fixed_state_goal_with_surface(goal, None)
    }

    fn focus_fixed_state_goal_with_surface(
        &self,
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
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
        // Resource compositions retain same-block separation compactly in
        // `PureFactContext`; materialize only the selected external
        // separation goal. This keeps the proof state proportional to its
        // checked inputs while making the kernel-certified, goal-indexed
        // projection an exact fact for the ordinary `Assumption` step.
        let facts = self.facts().with_selected_resource_separation(&goal);
        Ok(Self {
            context: self.context.clone(),
            state: KernelProofObject::root(self.state().locals.clone(), {
                let context = BranchState {
                    facts,
                    unfolded_predicates: match &outcome {
                        Some(_) => self.focused_branch_unfolds().clone(),
                        None => PersistentOrderedSet::default(),
                    },
                    execution: match &outcome {
                        Some(_) => self.branch_execution().cloned(),
                        None => None,
                    },
                };
                let presentation = PropositionPresentation {
                    surface: surface_goal.map(Arc::new),
                    surface_bindings: PersistentMap::default(),
                };
                let obligation = match outcome.clone() {
                    Some(outcome) => PropositionObligation::at_outcome(goal, presentation, outcome),
                    None => PropositionObligation::new(goal, presentation),
                };
                OpenBranch::new(Obligation::Proposition(obligation), context)
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
        })
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

    /// Completes externally owned fixed-state obligations against this frontier and
    /// exports their one structured certificate.
    ///
    /// Earlier checked descendants (notably `have` scopes) remain in the
    /// prefix. Each obligation is then independently selected and closed by
    /// an ordinary `Assumption` step against the accumulated persistent fact
    /// context. Certificate composition is therefore an audited terminal
    /// operation of `Proof`, not caller-owned syntax assembly.
    #[cfg(test)]
    pub(super) fn complete_fixed_state_obligations(
        &self,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        self.complete_fixed_state_obligations_inner(None, goals)
    }

    /// Completes the obligations with a certificate relative to `since`.
    ///
    /// An evolving outcome proof carries every earlier drained tactic in its
    /// lineage; those steps are recorded by their own tactics, so the grouped
    /// closure exports only the scope and closer work performed after the
    /// caller's checkpoint. A fresh grouped root passes its own root
    /// checkpoint and the two forms agree.
    pub(super) fn complete_fixed_state_obligations_since(
        &self,
        since: &ProofCheckpoint<'a>,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        self.complete_fixed_state_obligations_inner(Some(since), goals)
    }

    fn complete_fixed_state_obligations_inner(
        &self,
        since: Option<&ProofCheckpoint<'a>>,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        if goals.is_empty() {
            return Err(
                self.step_error("fixed-state obligation completion requires at least one goal")
            );
        }
        let fixed_state_context = matches!(self.context.as_ref(), ProofContext::FixedState(_))
            && matches!(self.focused_obligation(), Some(Obligation::Frontier(_)));
        let outcome_frontier = matches!(
            self.focused_obligation(),
            Some(Obligation::FunctionOutcome(_))
        );
        if !fixed_state_context && !outcome_frontier {
            return Err(self
                .step_error("fixed-state obligations require an open fixed-state proof context"));
        }
        let mut steps = match since {
            Some(since) => self.certificate_since(since)?.steps().to_vec(),
            None => self.certificate().steps().to_vec(),
        };
        for goal in goals {
            let closer = self
                .focus_fixed_state_surface_goal(goal)?
                .apply_step(ProofStep::Assumption)?;
            steps.extend_from_slice(closer.certificate().steps());
        }
        Ok(ProofCertificate::from_steps(steps))
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

    pub(in crate::lang::click::proof) fn active_unfolded_predicates(&self) -> Vec<String> {
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
            .expect("a complete proof derivation reaches its own root")
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
                self.step_error("certificate validationpoint belongs to a different proof context")
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
        let fact = self.lower_surface_proposition(surface, "`contradiction` fact")?;
        self.state
            .apply_contradiction(&fact)
            .map_err(|error| match error {
                PropositionCloseError::ContradictionUnavailable(fact) => self.step_error(format!(
                    "`contradiction` requires an exact fact and its exact negation or opposite condition polarity: {fact:?}"
                )),
                PropositionCloseError::Unavailable => {
                    self.step_error("`contradiction` requires an open proof branch")
                }
                _ => unreachable!("kernel returned an unrelated contradiction error"),
            })
    }

    fn proposition_goal(&self, message: &str) -> Result<&Proposition, ClickError> {
        self.goal().ok_or_else(|| self.step_error(message))
    }

    fn require_execution_frontier(&self, operation: &str) -> Result<(), ClickError> {
        (matches!(self.focused_obligation(), Some(Obligation::Frontier(_)))
            && !self.focused_loop_effect_closed())
        .then_some(())
        .ok_or_else(|| {
            self.step_error(format!(
                "{operation} cannot advance C execution inside a proposition proof"
            ))
        })
    }

    /// A structural-effect frame may retain its closed frontier only while
    /// resource scopes unwind. It remains addressable for those audited
    /// representation transitions, but it is no longer an open semantic goal.
    fn focused_loop_effect_closed(&self) -> bool {
        self.branch_execution()
            .and_then(|execution| execution.core.loop_effect_goal.as_ref())
            .is_some_and(|goal| goal.closed)
    }

    pub(in crate::lang::click::proof) fn step_error(
        &self,
        message: impl Into<String>,
    ) -> ClickError {
        ClickError::new(format!(
            "`{}` proof step {}: {}",
            self.context.claim_label(),
            self.node.depth,
            message.into()
        ))
    }

    #[cfg(test)]
    fn fact_lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.facts().lookup_comparisons(fact)
    }
}

/// The source-level form of one proof step, for diagnostics that point at a
/// line the user wrote.
fn proof_step_source_name(step: &ProofStep) -> &'static str {
    match step {
        ProofStep::Assumption => "assumption()",
        ProofStep::Normalize => "normalize()",
        ProofStep::Intro => "intro()",
        ProofStep::Split => "split()",
        ProofStep::Left => "left()",
        ProofStep::Right => "right()",
        ProofStep::Enumerate => "enumerate()",
        ProofStep::Step => "step",
        ProofStep::ApplyTheoremUsing { .. } => "apply",
        ProofStep::TransportUsing { .. } => "transport",
        ProofStep::InstantiateUsing { .. } => "instantiate",
        ProofStep::Have { .. } => "have",
        ProofStep::Rewrite(_) => "rewrite",
        ProofStep::Extract(_) => "extract",
        ProofStep::Contradiction(_) => "contradiction",
        ProofStep::Witness(_) => "witness",
        ProofStep::Choose(_) => "choose",
        ProofStep::UnfoldPredicate(_) | ProofStep::UnfoldResource(_) => "unfold",
        ProofStep::FoldResource(_) => "fold",
        ProofStep::ObserveResource(_) => "observe",
        ProofStep::FrameUsing { .. } => "frame",
        ProofStep::CloseInvariants => "close_invariants()",
        ProofStep::Mark(_) => "mark",
        _ => "tactic",
    }
}

mod construction;
mod execution_entry;
mod execution_joins;
mod execution_statements;
mod fact_index;
mod fixed_state_steps;
mod outcomes_and_focus;
mod provenance;
use provenance::{ProofCheckpoint, ProofNode, ProofStepOrigin};
mod resource_steps;
mod scope;
mod splits_and_scopes;
mod step_application;

#[cfg(test)]
mod tests;

pub(in crate::lang::click::proof) use fact_index::collect_surface_conjunct_leaves;
pub(in crate::lang::click::proof) use outcomes_and_focus::frontier_premise_anchor;

impl ExecutionProofPresentation {
    pub(in crate::lang::click::proof) fn defer_post_execution(
        &mut self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
    ) {
        self.post_execution_tactics
            .push(DeferredPostExecutionTactic {
                tactic_index,
                source_index,
                tactic,
                surface_recorded: false,
            });
    }

    /// Schedules ordered outcome work whose semantics and Surface provenance
    /// are already owned by a checked `Proof` descendant.
    pub(in crate::lang::click::proof) fn defer_checked_post_execution(
        &mut self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
    ) {
        self.post_execution_tactics
            .push(DeferredPostExecutionTactic {
                tactic_index,
                source_index,
                tactic,
                surface_recorded: true,
            });
    }
}
