use super::pure_theorems::{PureTheoremContext, lower_pure_theorem_proposition};
use super::*;
use crate::persistent::{PersistentMap, PersistentSet};

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
/// proposition, point, and execution-frontier goals use the same boundary.
#[derive(Clone)]
pub(super) struct Proof<'a> {
    context: Arc<ProofContext<'a>>,
    state: Arc<ProofState>,
    node: Arc<ProofNode>,
    /// The open goal this handle addresses. Focus is a cursor, not semantic
    /// state: two handles over one state may address different judgments,
    /// and checked operations advance exactly the focused goal.
    focused: GoalId,
}

/// An opaque position in one `Proof` derivation.
///
/// This retains no semantic state. Structured joins use it to extract only the
/// already-checked descendant steps for an arm.
#[derive(Clone)]
pub(super) struct ProofCheckpoint<'a> {
    context: Arc<ProofContext<'a>>,
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
    ids: [Option<GoalId>; 2],
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
    initial_continuation_depth: usize,
}

/// Bookkeeping for an exhaustive proof-level case split over execution
/// frontiers. The arms may be created from one shared frontier or may focus
/// the exhaustive successor partition already certified by the preceding
/// statement; either way, the `if` itself is logical rather than a C branch.
pub(super) struct ExecutionProofCaseSplit<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    ids: [GoalId; 2],
    surface_condition: ClickProposition,
    base_facts: [ProofFacts; 2],
    base_executions: [Arc<ExecutionProofState>; 2],
    path_facts: [Vec<Proposition>; 2],
    common_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    execution_start_state: CState,
    initial_continuation_depth: usize,
}

/// Bookkeeping for one logical `cases` split over an execution frontier.
/// Unlike an execution `if`, this split introduces the two exact disjuncts
/// from an already-available proposition and does not write a path choice
/// into the compatibility replay state.
pub(super) struct ExecutionLogicalCasesSplit<'a> {
    marker: ProofCheckpoint<'a>,
    split: SplitId,
    ids: [GoalId; 2],
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
}

/// The merged continuation a checked execution join produces: the shared
/// frontier context, the facts both arms established, and the structured
/// `Branch` step. Callers assemble the successor proof around it.
struct CheckedExecutionJoinParts {
    execution: ExecutionProofState,
    facts: ProofFacts,
    common_added_facts: Vec<Proposition>,
    unfolded_predicates: PersistentOrderedSet<String>,
    step: SimpleProofStep,
}

impl<'a> ExecutionSplit<'a> {
    /// `Some(take_then)` when the kernel certified exactly one feasible arm.
    pub(super) fn sole_feasible_arm(&self) -> Option<bool> {
        match self.ids {
            [Some(_), None] => Some(true),
            [None, Some(_)] => Some(false),
            _ => None,
        }
    }

    /// The recorded sibling goal id for one arm, when that arm is feasible.
    pub(super) fn arm_id(&self, take_then: bool) -> Option<GoalId> {
        self.ids[usize::from(!take_then)]
    }

    /// The structural preflight for `branch ensuring` on this split: a
    /// decided path always supports an interface, and a two-arm join does
    /// when the shared continuation is derivable and both arm snapshots
    /// descend from the parent's resource context.
    pub(super) fn supports_interface_branch(&self) -> bool {
        self.sole_feasible_arm().is_some()
            || (derive_execution_join_continuation(
                &self.parent_execution,
                &self.continuation_remaining,
                self.continuation_index,
            )
            .is_some()
                && self.base_executions.iter().flatten().all(|execution| {
                    execution
                        .state
                        .resources()
                        .descends_from(self.parent_execution.state.resources())
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
    ids: [GoalId; 2],
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
    initial_continuation_depth: usize,
    arms: [Option<PreparedExecutionArm>; 2],
}

struct PreparedExecutionArm {
    facts: ProofFacts,
    execution: ExecutionProofState,
    path_facts: Vec<Proposition>,
    introduced_facts: PersistentOrderedSet<Proposition>,
    condition_theorem: Theorem,
}

/// The exact nonterminal frontier reached after a checked C branch completes.
///
/// A branch at the end of an enclosing arm has no direct `remaining`
/// statement. In that case execution resumes by popping the already-owned
/// persistent continuation stack. Deriving that structural result from the
/// root lets both descendants be checked against one independently computed
/// frontier rather than selecting either arm's replay state.
#[derive(Clone)]
struct ExecutionBranchJoinContinuation {
    remaining: Arc<CStatement>,
    next_statement_index: usize,
    continuations: PersistentSequence<ProofExecutionContinuation>,
    completed_enclosing_branches: Vec<usize>,
}

/// Derives the exact nonterminal frontier reached after a checked C branch
/// completes, from the branch root's execution and recorded continuation
/// data. See [`ExecutionBranchJoinContinuation`].
fn derive_execution_join_continuation(
    root_execution: &ExecutionProofState,
    continuation_remaining: &Option<Arc<CStatement>>,
    continuation_index: usize,
) -> Option<ExecutionBranchJoinContinuation> {
    let mut continuations = root_execution.replay.frontier.continuations.clone();
    if let Some(remaining) = continuation_remaining {
        return Some(ExecutionBranchJoinContinuation {
            remaining: remaining.clone(),
            next_statement_index: continuation_index,
            continuations,
            completed_enclosing_branches: Vec::new(),
        });
    }

    let mut completed_enclosing_branches = Vec::new();
    while let Some(continuation) = continuations.pop() {
        if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
            completed_enclosing_branches.push(statement_index);
        }
        if let Some(remaining) = continuation.remaining {
            return Some(ExecutionBranchJoinContinuation {
                remaining,
                next_statement_index: continuation.next_statement_index,
                continuations,
                completed_enclosing_branches,
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
    },
    Open {
        resource: ResourceClause,
        source_index: usize,
        preserve_exposed_body: bool,
    },
}

fn explicit_linear_step(tactic: &ProofTactic) -> Option<SimpleProofStep> {
    match tactic {
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Some(SimpleProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::UnfoldPredicate(name) => Some(SimpleProofStep::UnfoldPredicate(name.clone())),
        ProofTactic::Witness(witness) => Some(SimpleProofStep::Witness(witness.clone())),
        ProofTactic::Choose(choice) => Some(SimpleProofStep::Choose(choice.clone())),
        ProofTactic::Assumption => Some(SimpleProofStep::Assumption),
        ProofTactic::Extract(proposition) => Some(SimpleProofStep::Extract(proposition.clone())),
        ProofTactic::Normalize => Some(SimpleProofStep::Normalize),
        ProofTactic::Intro => Some(SimpleProofStep::Intro),
        ProofTactic::Split => Some(SimpleProofStep::Split),
        ProofTactic::Left => Some(SimpleProofStep::Left),
        ProofTactic::Right => Some(SimpleProofStep::Right),
        ProofTactic::Enumerate => Some(SimpleProofStep::Enumerate),
        ProofTactic::Contradiction(proposition) => {
            Some(SimpleProofStep::Contradiction(proposition.clone()))
        }
        ProofTactic::Rewrite(proposition) => Some(SimpleProofStep::Rewrite(proposition.clone())),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Some(SimpleProofStep::TransportUsing {
            source: source.clone(),
            target: target.clone(),
            premises: premises.clone(),
        }),
        ProofTactic::InstantiateUsing {
            quantified,
            argument,
            premises,
        } => Some(SimpleProofStep::InstantiateUsing {
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

fn source_proof_is_supported(proof: &SourceProof) -> bool {
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
    fn from_steps(steps: &[SimpleProofStep]) -> Self {
        let Some((condition, then_proof, else_proof)) =
            steps.iter().rev().find_map(|step| match step {
                SimpleProofStep::If {
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

fn linear_script_is_supported(tactics: &[ProofTactic]) -> bool {
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

enum ProofContext<'a> {
    Pure(PureProofContext<'a>),
    Point(PointProofContext<'a>),
    Execution(ExecutionProofContext<'a>),
}

struct PureProofContext<'a> {
    claim_label: &'a str,
    theorem_context: &'a PureTheoremContext,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
}

struct PointProofContext<'a> {
    claim_label: &'a str,
    tactic_index: usize,
    parameters: &'a [syntax::C0Parameter],
    arguments: &'a [CExpression],
    pre_state: &'a CState,
    state: &'a CState,
    result: Option<&'a CValue>,
    premise_anchor: Option<ProgramPointRef>,
    program_point_states: &'a ProgramPointStates,
    surface_propositions: &'a SurfacePropositionMap,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    unfolded_predicates: &'a [String],
    effect_facts: &'a [ExecutionPureFact],
    lowering_context: Arc<Vec<Proposition>>,
    original_requirements: &'a [Requirement],
    requirement_label_indices: Option<&'a BTreeMap<String, usize>>,
    requirement_facts: &'a [Proposition],
}

struct ExecutionProofContext<'a> {
    claim_label: &'a str,
    tactic_index: usize,
    function_block: &'a FunctionBlock,
    function: &'a CFunction,
    parsed_function: &'a syntax::C0Function,
    arguments: &'a [CExpression],
    function_environment: &'a CExecutionEnvironment,
    resource_environment: &'a ResourceEnvironment,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
}

#[derive(Clone)]
struct ProofState {
    locals: ProofLocals,
    goals: ProofGoals,
    added_facts: Arc<Vec<Proposition>>,
    checked_facts: Arc<Vec<Proposition>>,
}

/// Identity of one open obligation within a proof lineage.
///
/// Allocation is monotonic per lineage. Ids allocated after divergent forks
/// may collide numerically; identity comparison is meaningful only along one
/// ancestry chain or against the recorded structure that allocated the id.
/// See the goal and split identity rules in
/// `design/proof-object-api.md`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct GoalId(u64);

impl GoalId {
    /// The id every fresh lineage allocates for its root obligation.
    const ROOT: Self = Self(1);
}

/// Identity of one audited split within a proof lineage.
///
/// A split allocates this id and its labeled child goal ids together, in rule
/// order, from the same lineage counter as ordinary goals. The recorded split
/// structure — not id magnitude — is what joins verify: each arm additionally
/// receives a unique entry provenance marker, so a checked descendant of one
/// split instance cannot be joined by another.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SplitId(u64);

/// The persistent typed goal collection owned by one `ProofState`, paired
/// with its lineage-local id allocator.
///
/// Every proof currently owns at most one open goal; the collection exists so
/// audited splits can record several labeled successor goals without a second
/// representation. A goal id names one obligation for its lifetime: focused
/// refinements preserve it, discharge retires it, and a retired id is never
/// reused within its lineage. Forks share the map root; a local update copies
/// only logarithmic paths.
#[derive(Clone)]
struct ProofGoals {
    open: PersistentMap<GoalId, Goal>,
    next_id: u64,
}

impl ProofGoals {
    /// Creates the root goal set of a fresh proof: one open goal under
    /// [`GoalId::ROOT`].
    fn root(goal: Goal) -> Self {
        Self {
            open: PersistentMap::default().with_inserted(GoalId::ROOT, goal),
            next_id: GoalId::ROOT.0 + 1,
        }
    }

    fn get(&self, at: GoalId) -> Option<&Goal> {
        self.open.get(&at)
    }

    /// Replaces the addressed goal's content while preserving its identity.
    /// This is the successor shape of a goal-preserving refinement rule.
    fn replace_at(&self, at: GoalId, goal: Goal) -> Self {
        debug_assert!(
            self.open.contains_key(&at),
            "goal refinement requires the addressed open goal"
        );
        Self {
            open: self.open.with_inserted(at, goal),
            next_id: self.next_id,
        }
    }

    /// Retires the addressed goal: the discharge shape of a goal-closing
    /// rule. The id is never reallocated within this lineage.
    fn discharge_at(&self, at: GoalId) -> Self {
        debug_assert!(
            self.open.contains_key(&at),
            "goal discharge requires the addressed open goal"
        );
        Self {
            open: self.open.without_key(&at),
            next_id: self.next_id,
        }
    }

    /// Replaces the addressed goal with labeled sibling goals in this same
    /// collection, in rule order: the parent id is retired by the split and
    /// each arm owns its recorded fresh id (identity rule 1); the siblings
    /// coexist in one state.
    fn split_at<const ARMS: usize>(
        &self,
        at: GoalId,
        arms: [Goal; ARMS],
    ) -> (SplitId, [GoalId; ARMS], Self) {
        debug_assert!(
            self.open.contains_key(&at),
            "an audited split requires the addressed open goal"
        );
        let split = SplitId(self.next_id);
        let ids: [GoalId; ARMS] = std::array::from_fn(|arm| GoalId(self.next_id + 1 + arm as u64));
        let mut open = self.open.without_key(&at);
        for (id, goal) in ids.iter().zip(arms) {
            open = open.with_inserted(*id, goal);
        }
        (
            split,
            ids,
            Self {
                open,
                next_id: self.next_id + 1 + ARMS as u64,
            },
        )
    }

    /// Retains the addressed goal under an updated path-local context,
    /// preserving identity, kind, and selection/content. This is the
    /// successor shape of a fact-adding or snapshot-updating rule.
    fn with_context_at(&self, at: GoalId, context: GoalContext) -> Self {
        let Some(goal) = self.get(at) else {
            unreachable!("a context successor requires the addressed open goal");
        };
        Self {
            open: self.open.with_inserted(at, goal.with_context(context)),
            next_id: self.next_id,
        }
    }

    /// Retains the addressed goal under updated facts, preserving any
    /// execution snapshot it already borrowed.
    fn with_facts_at(&self, at: GoalId, facts: ProofFacts) -> Self {
        let Some(goal) = self.get(at) else {
            unreachable!("a fact successor requires the addressed open goal");
        };
        self.with_context_at(
            at,
            GoalContext {
                facts,
                unfolded_predicates: goal.context().unfolded_predicates.clone(),
                execution: goal.context().execution.clone(),
            },
        )
    }

    /// Retains the addressed goal under an updated execution snapshot and
    /// facts. The successor preserves the goal's kind: a nested proposition
    /// judgment stated at a frontier may also refine facts.
    fn replace_execution_at(
        &self,
        at: GoalId,
        facts: ProofFacts,
        execution: ExecutionProofState,
    ) -> Self {
        let Some(goal) = self.get(at) else {
            unreachable!("an execution successor requires the addressed open goal");
        };
        self.with_context_at(
            at,
            GoalContext {
                facts,
                unfolded_predicates: goal.context().unfolded_predicates.clone(),
                execution: Some(Arc::new(execution)),
            },
        )
    }

    /// The strict frontier successor: the addressed goal must be an
    /// execution frontier. C-advancing rules use this shape; rules legal on
    /// nested proposition judgments use [`Self::replace_execution_at`].
    fn replace_frontier_at(
        &self,
        at: GoalId,
        facts: ProofFacts,
        execution: ExecutionProofState,
    ) -> Self {
        let Some(Goal::Frontier(_)) = self.get(at) else {
            unreachable!("a frontier transition requires the addressed frontier goal");
        };
        self.replace_execution_at(at, facts, execution)
    }

    /// Discharges the addressed goal when `complete` holds; otherwise the
    /// goal is retained under the updated facts. This is the successor shape
    /// of a fact-adding rule whose new fact may exactly close a proposition
    /// goal.
    fn discharged_if_at(&self, at: GoalId, complete: bool, facts: ProofFacts) -> Self {
        if complete {
            self.discharge_at(at)
        } else {
            self.with_facts_at(at, facts)
        }
    }

    /// Discharges the addressed goal when its proposition was established;
    /// otherwise retains it under the updated facts and execution snapshot.
    fn discharged_if_or_execution_at(
        &self,
        at: GoalId,
        complete: bool,
        facts: ProofFacts,
        execution: ExecutionProofState,
    ) -> Self {
        if complete {
            self.discharge_at(at)
        } else {
            self.replace_execution_at(at, facts, execution)
        }
    }

    fn is_discharged(&self) -> bool {
        self.open.is_empty()
    }
}

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
/// frontier state, legacy replay metadata, and persistent branch provenance.
#[derive(Clone)]
struct ExecutionProofState {
    state: SharedValue<CState>,
    replay: TacticReplayState,
    branch_path: PersistentSequence<String>,
    /// Kernel facts whose checked C-branch Surface spellings must survive a
    /// join for extraction and explicit historical premises.
    branch_surface_facts: PersistentOrderedSet<Proposition>,
    /// Decisions on the currently focused execution lineage. Forks append
    /// one entry in constant time.
    branch_decisions: PersistentSequence<ExecutionBranchDecision>,
    /// Path-local lineages aligned with terminal execution candidates. This
    /// is output-sized Proof provenance, never semantic state in a cursor.
    outcome_branch_decisions: Arc<Vec<PersistentSequence<ExecutionBranchDecision>>>,
    last_step_delta: ExecutionProofStepDelta,
    has_empty_execution_branch_leaf: bool,
}

#[derive(Clone)]
struct ExecutionBranchDecision {
    condition: ClickProposition,
    value: bool,
}

/// Read-only terminal data borrowed from an execution `Proof` by claim
/// finalization. This view carries no transition methods and owns no semantic
/// state; the `Proof` remains alive as the sole authority while finalization
/// checks its typed outcome goals.
pub(super) struct ProofFinalizationView<'p> {
    pub(super) state: &'p CState,
    pub(super) facts: Vec<Proposition>,
    pub(super) replay: &'p TacticReplayState,
    pub(super) branch_path: &'p PersistentSequence<String>,
    outcome_branch_decisions: &'p [PersistentSequence<ExecutionBranchDecision>],
}

impl ProofFinalizationView<'_> {
    /// Selects the retained surface branch skeleton for one checked outcome.
    /// Decisions are Proof provenance recorded at the typed splits; expansion
    /// reads them without reconstructing semantic facts from the post-state.
    pub(super) fn surface_branch_path(
        &self,
        path_index: usize,
        tactics: &[ProofTactic],
    ) -> Option<Vec<bool>> {
        let mut decisions = self.outcome_branch_decisions.get(path_index)?.iter().rev();
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

#[derive(Clone, Default)]
struct ExecutionProofStepDelta {
    function_entry_prerequisites: Vec<Proposition>,
    function_entry_derivations: Vec<Theorem>,
    unfolded_predicates: Vec<String>,
    statement_partition: Option<Arc<StatementSuccessorPartition>>,
}

/// Partition metadata attached only to the immediate successor of a checked
/// statement step. It is proof bookkeeping, not semantic authority: both arm
/// states and their polarity facts were already returned by the kernel-owned
/// transition checker.
#[derive(Clone)]
struct StatementSuccessorPartition {
    split: SplitId,
    ids: [GoalId; 2],
    condition: ConditionTerm,
    base_facts: [ProofFacts; 2],
    base_executions: [Arc<ExecutionProofState>; 2],
    path_facts: [Vec<Proposition>; 2],
    common_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    execution_start_state: CState,
    initial_continuation_depth: usize,
}

/// One unresolved judgment owned by a `Proof`.
///
/// A proposition goal can be discharged locally. An execution-frontier goal
/// remains open while fact-producing point steps advance the enclosing C
/// proof; later slices will add the frontier transition steps themselves.
#[derive(Clone)]
enum Goal {
    Proposition(PropositionGoal),
    Frontier(FrontierGoal),
    FunctionOutcome(OutcomeGoal),
}

/// The point-operation data a result-aware checker consumes, resolved from
/// either a point proof's borrowed context or a focused function-outcome
/// goal (see [`Proof::outcome_point_view`]).
/// Which effect-availability context an outcome-goal point operation
/// consumes; each migrated tactic matches its legacy drain input exactly.
#[derive(Clone, Copy)]
enum OutcomeEffectContext {
    Path,
    Replay,
}

#[derive(Clone, Copy)]
struct PointOperationView<'p> {
    claim_label: &'p str,
    tactic_index: usize,
    effect_facts: &'p [ExecutionPureFact],
    parameters: &'p [syntax::C0Parameter],
    arguments: &'p [CExpression],
    pre_state: &'p CState,
    state: &'p CState,
    result: Option<&'p CValue>,
    program_point_states: &'p ProgramPointStates,
    surface_propositions: &'p SurfacePropositionMap,
    predicate_environment: &'p PredicateEnvironment,
    click_function_environment: &'p ClickFunctionEnvironment,
    theorem_environment: &'p TheoremEnvironment,
    original_requirements: &'p [Requirement],
    requirement_label_indices: Option<&'p BTreeMap<String, usize>>,
    requirement_facts: &'p [Proposition],
}

impl<'p> PointOperationView<'p> {
    fn from_point(context: &'p PointProofContext<'_>) -> Self {
        Self {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: context.effect_facts,
            parameters: context.parameters,
            arguments: context.arguments,
            pre_state: context.pre_state,
            state: context.state,
            result: context.result,
            program_point_states: context.program_point_states,
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
/// directly instead of converting through the legacy replay adapter.
#[derive(Clone)]
struct OutcomeGoal {
    /// Zero-based position among the exit's checked paths, in the checked
    /// execution's deterministic order.
    path_index: usize,
    /// Effect clauses still owed by this exact checked outcome. Result-aware
    /// operations may advance the path before its source-ordered frame closes
    /// this selection.
    selection: EffectGoalSelection,
    /// Effect indices discharged by the most recent checked outcome frame.
    /// Ordered finalization consumes this private authority without checking
    /// the same effect transition again.
    checked_effects: Arc<Vec<usize>>,
    /// The outcome's result-aware point data. Behind one `Arc` so a nested
    /// proposition judgment stated at this outcome borrows it by identity;
    /// a checked operation that records new lowerings installs a fresh
    /// shared value atomically with its fact successor.
    point: Arc<OutcomePointData>,
    context: GoalContext,
}

/// The result-aware data one function outcome supplies to point operations:
/// its checked return value, post-outcome state, recorded surface
/// lowerings, and effect-availability facts.
#[derive(Clone)]
struct OutcomePointData {
    result: Arc<CValue>,
    state: SharedValue<CState>,
    surface_propositions: SurfacePropositionMap,
    effect_facts: Arc<Vec<ExecutionPureFact>>,
    /// The path's non-effect execution facts, matching the resource-fold law's
    /// historical input exactly.
    execution_pure_facts: Arc<Vec<ExecutionPureFact>>,
    /// The statement-entry anchor for premises naming a C local after it
    /// left scope, captured from the frontier at derivation.
    premise_anchor: Option<ProgramPointRef>,
    /// The lowered function-requirement facts in declaration order, captured
    /// as the raw prefix of the drain's working set at derivation: `choose`
    /// selects its source by requirement index, which persistent
    /// deduplication would misalign.
    requirement_facts: Arc<Vec<Proposition>>,
    /// Original proposition requirements keyed by their checked entry fact.
    /// Typed outcome evidence uses this persistent index to recover an exact
    /// function-entry Surface premise without scanning unrelated facts.
    requirement_surfaces: Arc<PersistentMap<Proposition, ClickProposition>>,
    branch_decisions: PersistentSequence<ExecutionBranchDecision>,
}

/// The path-local semantic context owned by one goal.
///
/// Facts and any execution snapshot travel together: sibling goals produced
/// by a split each own their path's context, sharing unchanged persistent
/// structure with the ancestor. `ProofState` retains only lineage-wide data.
#[derive(Clone)]
struct GoalContext {
    facts: ProofFacts,
    /// Predicate definitions activated by accepted proof-local unfold steps
    /// on this judgment's path. Inherited point/execution names remain in
    /// their shared context; this is only the path-local delta, so sibling
    /// goals unfold independently.
    unfolded_predicates: PersistentOrderedSet<String>,
    execution: Option<Arc<ExecutionProofState>>,
}

/// One open C frontier judgment and its path-local semantic context.
///
/// The execution state lives on the goal, not on the shared proof state, so
/// several simultaneous path-local judgments can coexist in one `Proof` once
/// splits produce them. The `Arc` makes forks and goal-preserving fact
/// refinements share the unchanged snapshot by identity.
#[derive(Clone)]
struct FrontierGoal {
    selection: EffectGoalSelection,
    context: GoalContext,
}

/// One proposition judgment keeps its checked kernel meaning and, when the
/// judgment originated in Surface Click, the exact syntax needed to refine
/// structural goals. Both values belong to the same immutable Proof state;
/// smart search must not carry a second caller-owned description of its goal.
#[derive(Clone)]
struct PropositionGoal {
    kernel: Arc<Proposition>,
    surface: Option<Arc<ClickProposition>>,
    /// Surface names introduced while refining this exact proposition goal.
    /// Universal binders are goal-local: sibling goals share the persistent
    /// map root at a split, then refine independently without leaking names.
    surface_bindings: PersistentMap<String, ContractExpression>,
    /// The judgment's path-local facts plus, when stated at an execution
    /// point, the immutable snapshot borrowed by identity from the frontier
    /// that stated it. A proposition goal can never publish a changed
    /// frontier through this context.
    context: GoalContext,
    /// Result-aware point data borrowed by identity from the function
    /// outcome this judgment was stated at, when it was. The judgment can
    /// read the outcome's result, state, and lowerings; it can never
    /// publish a changed outcome through this reference.
    outcome: Option<Arc<OutcomePointData>>,
}

impl Goal {
    fn proposition_in(context: GoalContext, kernel: Proposition) -> Self {
        Self::Proposition(PropositionGoal {
            kernel: Arc::new(kernel),
            surface: None,
            surface_bindings: PersistentMap::default(),
            context,
            outcome: None,
        })
    }

    fn surface_proposition_in(
        context: GoalContext,
        kernel: Proposition,
        surface: ClickProposition,
    ) -> Self {
        Self::Proposition(PropositionGoal {
            kernel: Arc::new(kernel),
            surface: Some(Arc::new(surface)),
            surface_bindings: PersistentMap::default(),
            context,
            outcome: None,
        })
    }

    /// A surface proposition judgment stated at one function outcome,
    /// borrowing that outcome's result-aware point data by identity.
    fn surface_proposition_at_outcome(
        context: GoalContext,
        outcome: Arc<OutcomePointData>,
        kernel: Proposition,
        surface: ClickProposition,
    ) -> Self {
        Self::Proposition(PropositionGoal {
            kernel: Arc::new(kernel),
            surface: Some(Arc::new(surface)),
            surface_bindings: PersistentMap::default(),
            context,
            outcome: Some(outcome),
        })
    }

    fn context(&self) -> &GoalContext {
        match self {
            Self::Proposition(goal) => &goal.context,
            Self::Frontier(goal) => &goal.context,
            Self::FunctionOutcome(goal) => &goal.context,
        }
    }

    fn with_context(&self, context: GoalContext) -> Self {
        match self {
            Self::Proposition(goal) => Self::Proposition(PropositionGoal {
                kernel: goal.kernel.clone(),
                surface: goal.surface.clone(),
                surface_bindings: goal.surface_bindings.clone(),
                context,
                outcome: goal.outcome.clone(),
            }),
            Self::Frontier(goal) => Self::Frontier(FrontierGoal {
                selection: goal.selection,
                context,
            }),
            Self::FunctionOutcome(goal) => Self::FunctionOutcome(OutcomeGoal {
                path_index: goal.path_index,
                selection: goal.selection,
                checked_effects: goal.checked_effects.clone(),
                point: goal.point.clone(),
                context,
            }),
        }
    }
}

/// Function-effect obligations owned alongside an execution frontier.
///
/// The selection is intentionally symbolic: grouped verification does not
/// copy every effect clause into every short-lived execution `Proof` root.
/// The immutable function block remains the indexed clause store.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum EffectGoalSelection {
    None,
    One(usize),
    All,
}

/// Private authority that the ordered outcome finalizer may consume without
/// proving the same function effect a second time.
///
/// Only checked `Proof` frame operations construct this value, after checking
/// every selected effect against the outcome or outcomes they own.
#[derive(Clone)]
pub(super) struct CheckedFrameAuthority {
    effect_indices: Arc<Vec<usize>>,
}

impl CheckedFrameAuthority {
    fn new(effect_indices: Vec<usize>) -> Self {
        Self {
            effect_indices: Arc::new(effect_indices),
        }
    }

    pub(super) fn contains(&self, effect_index: usize) -> bool {
        self.effect_indices.binary_search(&effect_index).is_ok()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.effect_indices.is_empty()
    }

    pub(super) fn len(&self) -> usize {
        self.effect_indices.len()
    }
}

#[derive(Clone, Copy)]
struct ProofStepOrigin {
    tactic_index: usize,
    source_index: usize,
}

/// Private persistent provenance node. Smart tactics can retain a `Proof`,
/// but cannot manufacture one of these or detach semantic state from the step
/// that produced it.
struct ProofNode {
    parent: Option<Arc<ProofNode>>,
    step: Option<Arc<SimpleProofStep>>,
    /// The goal the step advanced (or, for markers, introduced). Certificate
    /// extraction partitions an interleaved multi-goal derivation by this
    /// recorded attribution; it never infers ownership from final states.
    focused: GoalId,
    depth: usize,
}

/// Persistent semantic fact state shared by every `Proof` kind.
///
/// The exact index serves local simple-step queries and `assumptions` retains
/// the kernel's incrementally updated reasoning context. Forking shares both;
/// adding one fact copies only logarithmic index/context paths.
#[derive(Clone, Default)]
pub(super) struct ProofFacts {
    ordered: PersistentSequence<Proposition>,
    prioritized: Option<Arc<PrioritizedProofFacts>>,
    top_level_exact: PersistentSet<Proposition>,
    exact: PersistentSet<Proposition>,
    /// Every strict subtree of an available top-level conjunction. This is
    /// the exact structural authority for `extract`; top-level facts are not
    /// included merely because they are independently available.
    proper_conjuncts: PersistentSet<Proposition>,
    /// Atomic exact facts after the same direct-load normalization used by
    /// condition replay. This lets a branch reject its opposite path with an
    /// indexed lookup instead of scanning every unrelated fact.
    by_snapshot_blind: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>>,
    /// Exact true int32 equalities keyed by constant, variable, or interned
    /// memory-load operands. Keys have bounded comparison cost; a goal-local
    /// rewrite search walks only atoms named by the goal and their buckets.
    bitvector_equalities_by_atom:
        PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Proposition>>,
    by_quantified_replay: PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>>,
    /// Kernel-certified memory summaries for the selected execution
    /// frontier. Structural frame checking consumes these as transition
    /// evidence; they are not user premises and have no Surface spelling.
    memory_effect_summaries: PersistentSequence<Proposition>,
    /// Universal facts introduced specifically by a checked predicate unfold.
    /// Outcome smart search never probes ambient theorem or path universals.
    predicate_unfolded_universal_facts: PersistentSequence<Proposition>,
    implications_by_consequent:
        PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    assumptions: PureFactContext,
    implicit_transport_assumptions: PureFactContext,
    by_predicate: PersistentMap<String, PersistentSequence<Proposition>>,
}

/// A statement transition places its explicitly transported successor facts
/// before the ambient facts retained at their original snapshots. Prefix
/// batches preserve that semantic order without copying the ambient sequence.
struct PrioritizedProofFacts {
    parent: Option<Arc<PrioritizedProofFacts>>,
    facts: Arc<Vec<Proposition>>,
}

/// One indexed prefix of an available implication chain. The consequent key
/// selects this small candidate; checking still validates every antecedent
/// and the exact/snapshot-equivalent consequent against the current facts.
#[derive(Clone)]
struct ImplicationCandidate {
    antecedents: PersistentSequence<Proposition>,
    consequent: Proposition,
}

/// A bounded-comparison selector for equality rewrite provenance. Complex
/// arithmetic operands remain on the kernel-derivation path; this index covers
/// the atomic value/snapshot operands that outcome arithmetic rewrites need.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum BitvectorEqualityAtomKey {
    Constant(u32),
    Variable(Variable),
    MemoryLoad {
        memory: (u32, u32),
        pointer_hash: u64,
    },
}

/// An equality with an `old(...)` operand can use that entry expression's
/// reflexivity as an explicit transport source. Keep this selector
/// intentionally syntactic: the point checker remains the authority for
/// whether execution effects and result provenance permit the transport.
fn old_reflexive_transport_source(goal: &ClickProposition) -> Option<ClickProposition> {
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
    /// Reattributes subsequent execution-structure diagnostics to the source
    /// tactic that owns them without changing proof state or provenance.
    ///
    /// Simple steps carry their own origins. Structural operations span
    /// several checked transitions, so a long-lived function Proof updates
    /// this cursor metadata before entering each top-level structure.
    pub(super) fn with_execution_tactic_index(
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
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label: context.claim_label,
                tactic_index,
                function_block: context.function_block,
                function: context.function,
                parsed_function: context.parsed_function,
                arguments: context.arguments,
                function_environment: context.function_environment,
                resource_environment: context.resource_environment,
                predicate_environment: context.predicate_environment,
                click_function_environment: context.click_function_environment,
                theorem_environment: context.theorem_environment,
            })),
            state: self.state.clone(),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Restores an ancestor's exact execution diagnostic context after a
    /// nested structural operation. The descendant check is provenance-based;
    /// this changes no goals, facts, execution state, or proof nodes.
    pub(super) fn restore_execution_tactic_attribution(
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
            focused: self.focused,
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_pure_goal(
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
    pub(super) fn for_pure_surface_goal(
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
    fn for_pure_goal_with_surface(
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

                goals: ProofGoals::root({
                    let context = GoalContext {
                        facts,
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: None,
                    };
                    surface_goal
                        .map(|surface| {
                            Goal::surface_proposition_in(context.clone(), goal.clone(), surface)
                        })
                        .unwrap_or_else(|| Goal::proposition_in(context, goal))
                }),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_point_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_point(
            claim_label,
            tactic_index,
            available,
            |context| Goal::proposition_in(context, goal),
            parameters,
            arguments,
            pre_state,
            state,
            None,
            None,
            program_point_states,
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
    pub(super) fn for_point_surface_goal(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: Proposition,
        surface_goal: ClickProposition,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_point(
            claim_label,
            tactic_index,
            available,
            |context| Goal::surface_proposition_in(context, goal, surface_goal),
            parameters,
            arguments,
            pre_state,
            state,
            None,
            None,
            program_point_states,
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
    pub(super) fn for_point_goal_with_requirements(
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
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: &'a BTreeMap<String, usize>,
    ) -> Self {
        Self::for_point_goal_with_requirements_inner(
            claim_label,
            tactic_index,
            available,
            |context| Goal::proposition_in(context, goal),
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor,
            program_point_states,
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
    pub(super) fn for_point_surface_goal_with_requirements(
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
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: &'a BTreeMap<String, usize>,
    ) -> Self {
        Self::for_point_goal_with_requirements_inner(
            claim_label,
            tactic_index,
            available,
            |context| Goal::surface_proposition_in(context, goal, surface_goal),
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor,
            program_point_states,
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
    fn for_point_goal_with_requirements_inner(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: impl FnOnce(GoalContext) -> Goal,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<&ProgramPointRef>,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
        original_requirements: &'a [Requirement],
        requirement_label_indices: &'a BTreeMap<String, usize>,
    ) -> Self {
        Self::for_point(
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
            program_point_states,
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
    pub(super) fn for_point_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_point(
            claim_label,
            tactic_index,
            available,
            |context| {
                Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context,
                })
            },
            parameters,
            arguments,
            pre_state,
            state,
            result,
            None,
            program_point_states,
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
    pub(super) fn for_point_frontier_with_premise_anchor(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<&ProgramPointRef>,
        program_point_states: &'a ProgramPointStates,
        surface_propositions: &'a SurfacePropositionMap,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
        unfolded_predicates: &'a [String],
        effect_facts: &'a [ExecutionPureFact],
    ) -> Self {
        Self::for_point(
            claim_label,
            tactic_index,
            available,
            |context| {
                Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context,
                })
            },
            parameters,
            arguments,
            pre_state,
            state,
            result,
            premise_anchor.cloned(),
            program_point_states,
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
    fn for_point(
        claim_label: &'a str,
        tactic_index: usize,
        available: &'a [Proposition],
        goal: impl FnOnce(GoalContext) -> Goal,
        parameters: &'a [syntax::C0Parameter],
        arguments: &'a [CExpression],
        pre_state: &'a CState,
        state: &'a CState,
        result: Option<&'a CValue>,
        premise_anchor: Option<ProgramPointRef>,
        program_point_states: &'a ProgramPointStates,
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
        let goal = goal(GoalContext {
            facts,
            unfolded_predicates: PersistentOrderedSet::default(),
            execution: None,
        });
        let goal = match &goal {
            Goal::Proposition(proposition) => goal.with_context(GoalContext {
                facts: proposition
                    .context
                    .facts
                    .with_selected_load_equality_bridge(&proposition.kernel),
                unfolded_predicates: proposition.context.unfolded_predicates.clone(),
                execution: proposition.context.execution.clone(),
            }),
            Goal::Frontier(_) | Goal::FunctionOutcome(_) => goal.clone(),
        };
        Self {
            context: Arc::new(ProofContext::Point(PointProofContext {
                claim_label,
                tactic_index,
                parameters,
                arguments,
                pre_state,
                state,
                result,
                premise_anchor,
                program_point_states,
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

                goals: ProofGoals::root(goal),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        }
    }

    /// Creates an execution-frontier proof whose C state, replay metadata,
    /// facts, and provenance are structurally shared by checked descendants.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_execution_frontier(
        claim_label: &'a str,
        tactic_index: usize,
        execution: ProofReplayContext,
        function_block: &'a FunctionBlock,
        function: &'a CFunction,
        parsed_function: &'a syntax::C0Function,
        arguments: &'a [CExpression],
        function_environment: &'a CExecutionEnvironment,
        resource_environment: &'a ResourceEnvironment,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let effect_goals = match execution.replay.proof_site.as_ref() {
            Some(ProofSite::FunctionClaim {
                claim: CProofClaim::Grouped,
                ..
            }) if !function_block.effects().is_empty() => EffectGoalSelection::All,
            Some(ProofSite::FunctionClaim {
                claim: CProofClaim::Effect(index),
                ..
            }) => EffectGoalSelection::One(*index),
            _ => EffectGoalSelection::None,
        };
        Self::for_execution_frontier_with_effect_goals(
            claim_label,
            tactic_index,
            execution,
            effect_goals,
            function_block,
            function,
            parsed_function,
            arguments,
            function_environment,
            resource_environment,
            predicate_environment,
            click_function_environment,
            theorem_environment,
        )
    }

    /// Constructs an execution-frontier proof with an explicit effect-goal
    /// selection. The ordered outcome drain uses `EffectGoalSelection::None`:
    /// at the drain boundary the function frame has already been consumed
    /// into deferred checked authority, so the reconstructed frontier goal no
    /// longer carries effect obligations.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_execution_frontier_with_effect_goals(
        claim_label: &'a str,
        tactic_index: usize,
        execution: ProofReplayContext,
        effect_goals: EffectGoalSelection,
        function_block: &'a FunctionBlock,
        function: &'a CFunction,
        parsed_function: &'a syntax::C0Function,
        arguments: &'a [CExpression],
        function_environment: &'a CExecutionEnvironment,
        resource_environment: &'a ResourceEnvironment,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let ProofReplayContext {
            state,
            pure_facts,
            replay,
            branch_path,
        } = execution;
        Self {
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label,
                tactic_index,
                function_block,
                function,
                parsed_function,
                arguments,
                function_environment,
                resource_environment,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),

                goals: ProofGoals::root(Goal::Frontier(FrontierGoal {
                    selection: effect_goals,
                    context: GoalContext {
                        facts: ProofFacts::from_ordered(&pure_facts),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(ExecutionProofState {
                            state: state.into(),
                            replay: *replay,
                            branch_path,
                            branch_surface_facts: PersistentOrderedSet::default(),
                            branch_decisions: PersistentSequence::default(),
                            outcome_branch_decisions: Arc::new(Vec::new()),
                            last_step_delta: ExecutionProofStepDelta::default(),
                            has_empty_execution_branch_leaf: false,
                        })),
                    },
                })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        }
    }

    /// Derives one structural loop-effect obligation from an already checked
    /// preservation path. The new root shares the path's facts and execution
    /// snapshot; only the explicitly declared effect goal and its diagnostic
    /// source site are installed.
    pub(super) fn start_loop_effect_goal<'b>(
        &'b self,
        claim_label: &'b str,
        site: ProofSite,
        before_state: &CState,
        check: &CLoopEffectCheck,
    ) -> Result<Proof<'b>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("a loop effect requires an execution proof"));
        };
        self.require_execution_frontier("a loop effect")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("a loop effect lost its preservation state"))?;
        execution.replay.proof_site = Some(site);
        execution.replay.loop_effect_goal = Some(LoopEffectReplayGoal {
            before_state: before_state.clone(),
            check: check.clone(),
            closed: false,
        });
        execution.replay.proof_certificate_builder = ProofCertificateBuilder::default().into();
        execution.last_step_delta = ExecutionProofStepDelta::default();

        Ok(Proof {
            context: Arc::new(ProofContext::Execution(ExecutionProofContext {
                claim_label,
                tactic_index: 0,
                function_block: context.function_block,
                function: context.function,
                parsed_function: context.parsed_function,
                arguments: context.arguments,
                function_environment: context.function_environment,
                resource_environment: context.resource_environment,
                predicate_environment: context.predicate_environment,
                click_function_environment: context.click_function_environment,
                theorem_environment: context.theorem_environment,
            })),
            state: Arc::new(ProofState {
                locals: ProofLocals::default(),
                goals: ProofGoals::root(Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context: GoalContext {
                        facts: self.facts().clone(),
                        unfolded_predicates: PersistentOrderedSet::default(),
                        execution: Some(Arc::new(execution)),
                    },
                })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        })
    }

    /// The unique open goal, while every proof owns at most one. Readers
    /// that can only interpret a single focused goal go through here so the
    /// single-goal assumption stays in one place until splits arrive.
    fn focused_goal(&self) -> Option<&Goal> {
        self.state.goals.get(self.focused)
    }

    /// Whether the obligation this handle addresses has been discharged. On
    /// a single-goal proof this coincides with completion; inside a sibling
    /// split, only the focused obligation's discharge is an arm's success —
    /// the sibling legitimately remains open.
    pub(super) fn focused_discharged(&self) -> bool {
        self.state.goals.get(self.focused).is_none()
    }

    /// The focused goal's path-local execution context, shared by identity
    /// with the frontier that created it.
    fn goal_execution(&self) -> Option<&Arc<ExecutionProofState>> {
        self.focused_goal()?.context().execution.as_ref()
    }

    /// The focused goal's path-local unfold delta.
    fn focused_goal_unfolds(&self) -> &PersistentOrderedSet<String> {
        &self
            .focused_goal()
            .expect("unfold queries require an open goal")
            .context()
            .unfolded_predicates
    }

    /// The focused goal's path-local fact context. Every caller is a
    /// checked operation or search query on an open goal: `apply_step` and
    /// the structural operations reject discharged proofs first.
    fn facts(&self) -> &ProofFacts {
        match self.focused_goal() {
            Some(goal) => &goal.context().facts,
            None => unreachable!("fact queries require an open goal"),
        }
    }

    /// The focused goal's context with updated facts, for refinement rules
    /// that change goal content and facts together.
    fn refined_context(&self, facts: ProofFacts) -> GoalContext {
        GoalContext {
            facts,
            unfolded_predicates: self.focused_goal_unfolds().clone(),
            execution: self.goal_execution().cloned(),
        }
    }

    /// Rebuilds the focused proposition judgment with new content under the
    /// given context, preserving any outcome point data the judgment
    /// borrowed: a refinement changes what is claimed, never where it was
    /// stated.
    fn refined_proposition(
        &self,
        context: GoalContext,
        kernel: Proposition,
        surface: Option<ClickProposition>,
    ) -> Goal {
        let outcome = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => goal.outcome.clone(),
            Some(Goal::FunctionOutcome(goal)) => Some(goal.point.clone()),
            _ => None,
        };
        Goal::Proposition(PropositionGoal {
            kernel: Arc::new(kernel),
            surface: surface.map(Arc::new),
            surface_bindings: match self.focused_goal() {
                Some(Goal::Proposition(goal)) => goal.surface_bindings.clone(),
                _ => PersistentMap::default(),
            },
            context,
            outcome,
        })
    }

    fn execution(&self) -> Option<&ExecutionProofState> {
        self.goal_execution().map(Arc::as_ref)
    }

    #[cfg(test)]
    fn goals_next_id(&self) -> u64 {
        self.state.goals.next_id
    }

    #[cfg(test)]
    fn outcome_result(&self) -> Option<&CValue> {
        match self.focused_goal()? {
            Goal::FunctionOutcome(goal) => Some(goal.point.result.as_ref()),
            _ => None,
        }
    }

    pub(super) fn goal(&self) -> Option<&Proposition> {
        match self.focused_goal() {
            Some(Goal::Proposition(goal)) => Some(&goal.kernel),
            _ => None,
        }
    }

    fn surface_goal(&self) -> Option<&ClickProposition> {
        match self.focused_goal() {
            Some(Goal::Proposition(goal)) => goal.surface.as_deref(),
            _ => None,
        }
    }

    /// Number of selected function-effect obligations represented by this
    /// frontier without materializing their clauses.
    #[cfg(test)]
    fn effect_goal_count(&self) -> usize {
        let Some(Goal::Frontier(FrontierGoal { selection, .. })) = self.focused_goal() else {
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
    /// point-frontier context without rebuilding its persistent facts.
    ///
    /// Grouped contract finalization owns several independent ensure goals;
    /// this audited root operation focuses one of them while sharing the
    /// checked outcome context. It is not a proof transition and therefore
    /// starts fresh provenance. A point-frontier descendant may have published
    /// checked `have` facts before another external obligation is selected;
    /// a proof that already owns a proposition goal cannot replace it.
    pub(super) fn focus_point_goal(&self, goal: Proposition) -> Result<Self, ClickError> {
        self.focus_point_goal_with_surface(goal, None)
    }

    fn focus_point_goal_with_surface(
        &self,
        goal: Proposition,
        surface_goal: Option<ClickProposition>,
    ) -> Result<Self, ClickError> {
        let point_frontier = matches!(self.context.as_ref(), ProofContext::Point(_))
            && matches!(self.focused_goal(), Some(Goal::Frontier(_)));
        // A function-outcome goal is itself a result-aware point frontier:
        // an externally owned obligation focused from it borrows the
        // outcome's point data by identity, exactly like a nested `have`.
        let outcome = match self.focused_goal() {
            Some(Goal::FunctionOutcome(outcome_goal)) => Some(outcome_goal.point.clone()),
            _ => None,
        };
        if !point_frontier && outcome.is_none() {
            return Err(
                self.step_error("a proposition goal can be focused only from a point frontier")
            );
        }
        // Resource compositions retain same-block separation compactly in
        // `PureFactContext`; materialize only the selected external
        // separation goal. This keeps the proof state proportional to its
        // checked inputs while making the kernel-certified, goal-indexed
        // projection an exact fact for the ordinary `Assumption` step.
        let facts = self.facts().with_selected_resource_separation(&goal);
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals: ProofGoals::root({
                    let context = GoalContext {
                        facts,
                        unfolded_predicates: match &outcome {
                            Some(_) => self.focused_goal_unfolds().clone(),
                            None => PersistentOrderedSet::default(),
                        },
                        execution: match &outcome {
                            Some(_) => self.goal_execution().cloned(),
                            None => None,
                        },
                    };
                    Goal::Proposition(PropositionGoal {
                        kernel: Arc::new(goal),
                        surface: surface_goal.map(Arc::new),
                        surface_bindings: PersistentMap::default(),
                        context,
                        outcome,
                    })
                }),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        })
    }

    /// Lowers and selects one externally owned Surface Click obligation from
    /// a point frontier. The returned proof shares every accumulated checked
    /// fact but owns fresh provenance for that obligation's closing steps.
    pub(super) fn focus_point_surface_goal(
        &self,
        goal: &ClickProposition,
    ) -> Result<Self, ClickError> {
        let kernel = self.lower_surface_goal(goal, "point obligation")?;
        self.focus_point_goal_with_surface(kernel, Some(goal.clone()))
    }

    /// Completes externally owned point obligations against this frontier and
    /// exports their one structured certificate.
    ///
    /// Earlier checked descendants (notably `have` scopes) remain in the
    /// prefix. Each obligation is then independently selected and closed by
    /// an ordinary `Assumption` step against the accumulated persistent fact
    /// context. Certificate composition is therefore an audited terminal
    /// operation of `Proof`, not caller-owned syntax assembly.
    pub(super) fn complete_point_obligations(
        &self,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        self.complete_point_obligations_inner(None, goals)
    }

    /// Completes the obligations with a certificate relative to `since`.
    ///
    /// An evolving outcome proof carries every earlier drained tactic in its
    /// lineage; those steps are recorded by their own tactics, so the grouped
    /// closure exports only the scope and closer work performed after the
    /// caller's checkpoint. A fresh grouped root passes its own root
    /// checkpoint and the two forms agree.
    pub(super) fn complete_point_obligations_since(
        &self,
        since: &ProofCheckpoint<'a>,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        self.complete_point_obligations_inner(Some(since), goals)
    }

    fn complete_point_obligations_inner(
        &self,
        since: Option<&ProofCheckpoint<'a>>,
        goals: &[ClickProposition],
    ) -> Result<ProofCertificate, ClickError> {
        if goals.is_empty() {
            return Err(self.step_error("point obligation completion requires at least one goal"));
        }
        let point_frontier = matches!(self.context.as_ref(), ProofContext::Point(_))
            && matches!(self.focused_goal(), Some(Goal::Frontier(_)));
        let outcome_frontier = matches!(self.focused_goal(), Some(Goal::FunctionOutcome(_)));
        if !point_frontier && !outcome_frontier {
            return Err(self.step_error("point obligations require an open point frontier"));
        }
        let mut steps = match since {
            Some(since) => self.certificate_since(since)?.steps().to_vec(),
            None => self.certificate().steps().to_vec(),
        };
        for goal in goals {
            let closer = self
                .focus_point_surface_goal(goal)?
                .apply_step(SimpleProofStep::Assumption)?;
            steps.extend_from_slice(closer.certificate().steps());
        }
        Ok(ProofCertificate::from_steps(steps))
    }

    pub(super) fn is_complete(&self) -> bool {
        self.state.goals.is_discharged()
    }

    fn active_unfolded_predicates(&self) -> Vec<String> {
        let inherited = match self.context.as_ref() {
            ProofContext::Pure(_) => &[][..],
            ProofContext::Point(context) => context.unfolded_predicates,
            ProofContext::Execution(_) => self
                .execution()
                .map(|execution| execution.replay.unfolded_predicates.as_slice())
                .unwrap_or(&[]),
        };
        let mut names = inherited.to_vec();
        let mut seen = inherited.iter().cloned().collect::<BTreeSet<_>>();
        for name in self.focused_goal_unfolds() {
            if seen.insert(name.clone()) {
                names.push(name.clone());
            }
        }
        names
    }

    /// Checks one explicit simple step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(super) fn apply_step(&self, step: SimpleProofStep) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, None)
    }

    /// Applies a step while retaining its source occurrence for any ordered
    /// terminal work the checked transition has to schedule. The source site
    /// affects diagnostics and finalization order only; the certificate node
    /// remains exactly the supplied `SimpleProofStep`.
    fn apply_step_with_origin(
        &self,
        step: SimpleProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin_mode(step, origin, false)
    }

    /// Applies one step while optionally retaining a closed structural-effect
    /// frontier long enough for enclosing resource scopes to close. That
    /// retained frontier is sealed: only `ProofScope::join_inner` may consume
    /// it, and the outermost resource join retires the goal.
    fn apply_step_with_origin_mode(
        &self,
        step: SimpleProofStep,
        origin: Option<ProofStepOrigin>,
        retain_closed_loop_effect_goal: bool,
    ) -> Result<Self, ClickError> {
        if self.focused_discharged() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                simple_step_source_name(&step)
            )));
        }
        if self.focused_loop_effect_closed() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                simple_step_source_name(&step)
            )));
        }

        if let SimpleProofStep::Have { proposition, proof } = &step {
            return self.apply_have_step(proposition, proof);
        }
        if let SimpleProofStep::Step = &step {
            return self.apply_execution_statement_step(step, &[]);
        }
        if let SimpleProofStep::StepUsing(premises) = &step {
            return self.apply_execution_statement_step(step.clone(), premises);
        }

        let next_state = match &step {
            SimpleProofStep::Mark(name) => self.apply_execution_mark(name),
            SimpleProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            SimpleProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            SimpleProofStep::UnfoldPredicate(name) => self.apply_predicate_unfold(name),
            SimpleProofStep::UnfoldResource(resource) => {
                self.apply_execution_resource_unfold(resource)
            }
            SimpleProofStep::FoldResource(resource) => {
                if self.focused_outcome_point().is_some() {
                    self.apply_outcome_resource_fold(resource)
                } else {
                    self.apply_execution_resource_fold(resource)
                }
            }
            SimpleProofStep::ObserveResource(resource) => {
                self.apply_execution_resource_observation(resource)
            }
            SimpleProofStep::Choose(choice) => self.apply_point_choose(choice),
            SimpleProofStep::Witness(witness) => self.apply_point_witness(witness),
            SimpleProofStep::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => self.apply_point_instantiate_using(quantified, argument, premises),
            SimpleProofStep::Extract(proposition) => self.apply_extract(proposition),
            SimpleProofStep::Rewrite(equality) => self.apply_rewrite(equality),
            SimpleProofStep::Assumption => self.apply_assumption(),
            SimpleProofStep::Normalize => self.apply_normalize(),
            SimpleProofStep::Intro => self.apply_intro(),
            SimpleProofStep::Split => self.apply_split(),
            SimpleProofStep::Left => self.apply_left(),
            SimpleProofStep::Right => self.apply_right(),
            SimpleProofStep::Enumerate => self.apply_enumerate(),
            SimpleProofStep::Contradiction(surface) => self.apply_contradiction(surface),
            SimpleProofStep::CloseInvariants => self.apply_close_invariants(),
            SimpleProofStep::FrameUsing { region, premises } => {
                if self.focused_outcome_point().is_some() {
                    self.apply_outcome_frame_using(region.as_ref(), premises)
                } else {
                    self.apply_execution_frame_using(
                        region.as_ref(),
                        premises,
                        origin,
                        retain_closed_loop_effect_goal,
                    )
                }
            }
            _ => {
                Err(self
                    .step_error("this simple step has not yet migrated to the checked `Proof` API"))
            }
        }?;

        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(next_state),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused: self.focused,
                depth: self.node.depth + 1,
            }),
            focused: self.focused,
        })
    }

    /// Applies one explicit `Have` through the same owned scope operations as
    /// a source `have` block. Each body step advances the scope's persistent
    /// child `Proof`; joining publishes only the checked proposition and
    /// retains the body's exact surface operations as provenance. A failed
    /// body leaves this immutable root untouched.
    fn apply_have_step(
        &self,
        proposition: &ClickProposition,
        proof: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        let mut scope = self.begin_have(proposition.clone())?;
        for step in proof.steps() {
            scope = scope.apply_step(step.clone())?;
        }
        scope.join()
    }

    fn selected_effect_indices(
        &self,
        context: &ExecutionProofContext<'_>,
    ) -> Result<Vec<usize>, ClickError> {
        let selection = match self.focused_goal() {
            Some(Goal::Frontier(FrontierGoal { selection, .. })) => *selection,
            Some(Goal::FunctionOutcome(OutcomeGoal { selection, .. })) => *selection,
            _ => {
                return Err(self.step_error("`frame using` requires an execution effect goal"));
            }
        };
        let effect_count = context.function_block.effects().len();
        let indices = match selection {
            EffectGoalSelection::None => Vec::new(),
            EffectGoalSelection::One(index) if index < effect_count => vec![index],
            EffectGoalSelection::One(index) => {
                return Err(self.step_error(format!(
                    "selected effect goal {index} does not exist; the function has {effect_count} effect clauses"
                )));
            }
            EffectGoalSelection::All => (0..effect_count).collect(),
        };
        if indices.is_empty() {
            return Err(self.step_error("`frame using` has no function effect goal to prove"));
        }
        Ok(indices)
    }

    /// Whether a transitional driver may check and then export this frame
    /// step. Empty mutable function frames stay out of that adapter: their
    /// exact `Proof` meaning differs from the legacy ambient-fact behavior,
    /// so checking one before compatibility replay would apply earlier smart
    /// operations twice. An authoritative Proof unit applies the exact step
    /// directly instead of consulting this compatibility query.
    fn supports_checked_execution_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(false);
        };
        if !matches!(region, None | Some(CodeRegionRef::Function)) {
            return Ok(true);
        }
        if !premises.is_empty() {
            return Ok(true);
        }
        let effect_indices = self.selected_effect_indices(context)?;
        Ok(effect_indices.iter().all(|index| {
            matches!(
                context.function_block.effects()[*index].effect(),
                Effect::Immutable
            )
        }))
    }

    /// Checks one explicit function-level frame step exactly once and records
    /// private authority for the ordered outcome finalizer. Keep this rule
    /// outlined so its execution-state locals do not enlarge the common
    /// simple-step dispatcher frame; the expansion small-stack test pins that
    /// dispatch budget.
    #[inline(never)]
    fn apply_outcome_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`frame using` requires an execution proof"));
        };
        if !matches!(region, None | Some(CodeRegionRef::Function)) {
            return Err(
                self.step_error("a result-aware `frame using` can close only the function effect")
            );
        }
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("result-aware `frame using` requires an outcome goal"));
        };
        let effect_indices = self.selected_effect_indices(context)?;
        let execution = goal.context.execution.as_deref().ok_or_else(|| {
            self.step_error("result-aware `frame using` lost its execution snapshot")
        })?;
        let pre_state = execution.replay.execution_start_state(&execution.state);

        let mut point = (*goal.point).clone();
        let mut frame_facts = Vec::with_capacity(premises.len());
        for surface in premises {
            let fact = point
                .surface_propositions
                .available_kernel_matching(surface, |kernel| self.facts().contains(kernel))
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    self.lower_surface_proposition(surface, "`frame using` premise")
                })?;
            if !self.facts().contains(&fact) {
                return Err(self.step_error(format!(
                    "`frame using` requires an exact available premise: {fact:?}"
                )));
            }
            point.surface_propositions.record_lowering(surface, &fact)?;
            if !frame_facts.contains(&fact) {
                frame_facts.push(fact);
            }
        }

        let mut outcome = CFunctionOutcome::Return {
            value: (*point.result).clone(),
            state: (*point.state).clone(),
        };
        for effect_index in &effect_indices {
            let claim = FunctionClaimRef::Effect(
                *effect_index,
                &context.function_block.effects()[*effect_index],
            );
            let claim_label =
                function_claim_label(context.function_block.signature().name(), &claim);
            check_effect_claim_exact(
                &claim_label,
                goal.path_index,
                &point.effect_facts,
                &frame_facts,
                &claim,
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                &outcome,
            )?;
        }

        let mut assumptions = self.facts().assumptions().clone();
        for fact in point.effect_facts.iter() {
            assumptions = assumptions.assume_proposition(fact.proposition().clone());
        }
        let (transitioned, _obligations) =
            crate::kernel::apply_c_function_contract_resource_transition(
                pre_state,
                context.function,
                context.arguments,
                outcome,
                &assumptions,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not apply checked contract resource effect: {message}"
                ))
            })?;
        outcome = transitioned;
        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(self.step_error(
                "checked contract resource effect did not preserve the return outcome",
            ));
        };
        point.result = Arc::new(value);
        point.state = state.into();
        let mut updated = goal.clone();
        updated.selection = EffectGoalSelection::None;
        updated.checked_effects = Arc::new(effect_indices);
        updated.point = Arc::new(point);
        Ok(ProofState {
            locals: self.state.locals.clone(),
            goals: self
                .state
                .goals
                .replace_at(self.focused, Goal::FunctionOutcome(updated)),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(frame_facts),
        })
    }

    #[inline(never)]
    fn apply_execution_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
        origin: Option<ProofStepOrigin>,
        retain_closed_loop_effect_goal: bool,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`frame using` requires an execution proof"));
        };
        self.require_execution_frontier("`frame using`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;

        let mut frame_facts = Vec::with_capacity(premises.len());
        for surface in premises {
            let fact = execution
                .replay
                .surface_propositions
                .available_kernel_matching(surface, |kernel| {
                    self.facts()
                        .replay_available_across_effects(kernel, &execution.replay.effect_facts)
                })
                .cloned()
                .map(Ok)
                .unwrap_or_else(|| {
                    self.lower_surface_proposition(surface, "`frame using` premise")
                })?;
            if !self
                .facts()
                .replay_available_across_effects(&fact, &execution.replay.effect_facts)
            {
                return Err(self.step_error(format!(
                    "`frame using` requires an exact available premise: {fact:?}"
                )));
            }
            execution
                .replay
                .surface_propositions
                .record_lowering(surface, &fact)?;
            if !frame_facts.contains(&fact) {
                frame_facts.push(fact);
            }
        }
        if execution.replay.loop_effect_goal.is_some() {
            if region.is_some() {
                return Err(
                    self.step_error("a structural effect proof must use unqualified `frame using`")
                );
            }
            let goal = execution
                .replay
                .loop_effect_goal
                .as_ref()
                .expect("the loop effect goal was observed above");
            if goal.closed {
                return Err(self.step_error("the structural effect goal was closed more than once"));
            }
            let mut loop_effect_facts = frame_facts.clone();
            loop_effect_facts.extend(
                execution
                    .replay
                    .effect_facts
                    .iter()
                    .map(|fact| fact.proposition().clone()),
            );
            loop_effect_facts.extend(self.facts().memory_effect_summaries().cloned());
            loop_effect_facts.sort();
            loop_effect_facts.dedup();
            c_loop_effects_hold_at_back_edge(
                &goal.before_state,
                &execution.state,
                std::slice::from_ref(&goal.check),
                &loop_effect_facts,
                &assumptions_from_propositions(&loop_effect_facts),
            )
            .map_err(|message| self.step_error(format!("`frame using` failed: {message}")))?;
            execution
                .replay
                .loop_effect_goal
                .as_mut()
                .expect("the checked loop effect goal remains present")
                .closed = true;
            let goals = if retain_closed_loop_effect_goal {
                self.state
                    .goals
                    .replace_frontier_at(self.focused, self.facts().clone(), execution)
            } else {
                self.state.goals.discharge_at(self.focused)
            };
            return Ok(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(frame_facts),
            });
        }
        if !execution.replay.is_at_function_exit() {
            return Err(self.step_error("`frame using` requires function exit"));
        }
        if let Some(region) = region {
            // Loop effect clauses are declared by frontier-local `loop`
            // tactics. Bind the exact clauses already checked on this replay
            // before resolving labels or validating the qualified frame.
            let frame_function_block =
                (!execution.replay.frontier_loop_clauses.is_empty()).then(|| {
                    context.function_block.with_bound_frontier_loop_clauses(
                        &execution.replay.frontier_loop_clauses.to_vec(),
                    )
                });
            let frame_function_block = frame_function_block
                .as_ref()
                .unwrap_or(context.function_block);
            let resolved = resolve_code_region_ref(
                frame_function_block,
                region,
                context.claim_label,
                context.tactic_index,
            )?;
            if !matches!(resolved, CodeRegion::Function) {
                validate_qualified_frame_code_region(
                    frame_function_block,
                    context.parsed_function,
                    resolved,
                    context.claim_label,
                    origin.map_or(context.tactic_index, |origin| origin.tactic_index),
                )?;
                let origin = origin.unwrap_or(ProofStepOrigin {
                    tactic_index: context.tactic_index,
                    source_index: context.tactic_index,
                });
                execution.replay.defer_checked_post_execution(
                    origin.tactic_index,
                    origin.source_index,
                    PostExecutionTactic::FrameRegion(region.clone()),
                );
                execution.last_step_delta = ExecutionProofStepDelta::default();
                return Ok(ProofState {
                    locals: self.state.locals.clone(),

                    goals: self.state.goals.replace_frontier_at(
                        self.focused,
                        self.facts().clone(),
                        execution,
                    ),
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                });
            }
        }

        let effect_indices = self.selected_effect_indices(context)?;

        let checked_execution = execution.replay.execution().ok_or_else(|| {
            self.step_error("function-exit proof has no checked execution outcomes")
        })?;
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        for effect_index in &effect_indices {
            let claim = FunctionClaimRef::Effect(
                *effect_index,
                &context.function_block.effects()[*effect_index],
            );
            validate_function_frame_tactic(
                checked_execution,
                &claim,
                context.claim_label,
                origin.map_or(context.tactic_index, |origin| origin.tactic_index),
                context.parsed_function.parameters(),
                context.arguments,
                &pre_state,
                &frame_facts,
            )?;
        }

        let origin = origin.unwrap_or(ProofStepOrigin {
            tactic_index: context.tactic_index,
            source_index: context.tactic_index,
        });
        execution.replay.defer_checked_post_execution(
            origin.tactic_index,
            origin.source_index,
            PostExecutionTactic::CheckedFrameUsing {
                authority: CheckedFrameAuthority::new(effect_indices),
                region: region.cloned(),
                premises: premises.to_vec(),
                surface_tactics: None,
            },
        );
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(
                self.focused,
                Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context: GoalContext {
                        facts: self.facts().clone(),
                        unfolded_predicates: self.focused_goal_unfolds().clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
            ),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Applies a planner-selected contextual frame tree directly to this
    /// Proof. The plan carries only Surface operations and branch shape; it
    /// owns no facts, execution state, or semantic successor authority.
    fn apply_contextual_frame_plan(
        &self,
        plan: &ContextualFramePlan,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        let ContextualFramePlan::If {
            condition,
            then_plan,
            else_plan,
        } = plan
        else {
            let ContextualFramePlan::Leaf(leaf) = plan else {
                unreachable!()
            };
            return self.apply_contextual_frame_leaf_plan(leaf, origin);
        };
        let (split, record) = self.split_focused_outcome_if(condition.clone())?;
        let advanced = split
            .focus_outcome_arm(&record, 0)?
            .apply_contextual_frame_plan(then_plan, origin)?
            .focus_outcome_arm(&record, 1)?
            .apply_contextual_frame_plan(else_plan, origin)?;
        advanced.join_focused_outcome_if(&record)
    }

    fn apply_contextual_frame_leaf_plan(
        &self,
        plan: &ContextualFrameLeafPlan,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        let mut checked = self.clone();
        for have in &plan.haves {
            let scope = checked.begin_have(have.proposition.clone())?;
            let Some(scope) = scope.try_planned_linear_script(&have.tactics)? else {
                return Err(checked.step_error(
                    "contextual frame `have` plan did not complete through checked Proof operations",
                ));
            };
            checked = scope.join()?;
        }
        checked.apply_step_with_origin(
            SimpleProofStep::FrameUsing {
                region: None,
                premises: plan.premises.clone(),
            },
            origin,
        )
    }

    /// Recovers only the latest checked branch shape from persistent Proof
    /// provenance. Contextual-frame search needs this path partition, not a
    /// materialized certificate for the complete derivation.
    fn contextual_frame_skeleton(&self) -> ContextualFrameSkeleton {
        let mut node = Some(self.node.as_ref());
        while let Some(current) = node {
            if let Some(step) = current.step.as_deref() {
                if matches!(step, SimpleProofStep::If { .. }) {
                    return ContextualFrameSkeleton::from_steps(std::slice::from_ref(step));
                }
            }
            node = current.parent.as_deref();
        }
        ContextualFrameSkeleton::Leaf
    }

    /// Uses the contextual footprint planner only to select a typed tree of
    /// Surface operations. The plan has performed no semantic transition and
    /// contains no certificate builder or replay-owned proof state.
    fn select_contextual_frame_candidate(&self) -> Result<Option<ContextualFramePlan>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let execution_state = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if !execution_state.replay.is_at_function_exit()
            || !execution_state.replay.case_assumptions.is_empty()
        {
            return Ok(None);
        }
        let effect_indices = self.selected_effect_indices(context)?;
        let execution = execution_state.replay.execution().ok_or_else(|| {
            self.step_error("function-exit proof has no checked execution outcomes")
        })?;
        let path_independent_only = self.node.depth == 0
            && (execution.paths().len() > 1
                || execution_state.replay.has_structured_branch_history);
        let available = self.facts().to_vec();
        let pre_state = execution_state
            .replay
            .old_reference_state(&execution_state.state);
        let mut path_derivations = Vec::with_capacity(execution.paths().len());
        for (path_index, path) in execution.paths().iter().enumerate() {
            if !path.obligations().is_empty() {
                return Err(self.step_error(
                    "`frame` cannot plan from an execution path with unresolved obligations",
                ));
            }
            let mut path_facts = available.clone();
            path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
            let implicit_path_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            let mut combined = Vec::new();
            for effect_index in &effect_indices {
                for derivation in plan_effect_clause_derivations(
                    context.claim_label,
                    path_index,
                    path.effect_facts(),
                    &path_facts,
                    &implicit_path_facts,
                    context.function_block.effects()[*effect_index].effect(),
                    context.parsed_function.parameters(),
                    context.arguments,
                    pre_state,
                    path.outcome(),
                )? {
                    if !combined.contains(&derivation) {
                        combined.push(derivation);
                    }
                }
            }
            path_derivations.push(combined);
        }
        let skeleton = self.contextual_frame_skeleton();
        let mut construction_replay = execution_state.replay.clone();
        let mut branch_conditions = Vec::new();
        skeleton.collect_conditions(&mut branch_conditions);
        for condition in &branch_conditions {
            let negated = ClickProposition::Not(Box::new(condition.clone()));
            let mut surface_forms = vec![condition.clone(), negated.clone()];
            for candidate in [
                reverse_surface_comparison(condition),
                reverse_surface_comparison(&negated),
            ]
            .into_iter()
            .flatten()
            {
                if !surface_forms.contains(&candidate) {
                    surface_forms.push(candidate);
                }
            }
            for (path_index, path) in execution.paths().iter().enumerate() {
                let CFunctionOutcome::Return {
                    value: result,
                    state: post_state,
                } = path.outcome()
                else {
                    return Err(self.step_error(format!(
                        "execution path {path_index} cannot decide a proof branch without a return outcome"
                    )));
                };
                let mut path_facts = available.clone();
                path_facts.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                for surface in &surface_forms {
                    let kernel = lower_outcome_proposition_with_program_points(
                        context.parsed_function.parameters(),
                        context.arguments,
                        pre_state,
                        post_state,
                        result,
                        &path_facts,
                        surface,
                        context.predicate_environment,
                        context.click_function_environment,
                        &execution_state.replay.program_point_states,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not lower execution outcome branch condition: {message}"
                        ))
                    })?;
                    construction_replay
                        .surface_propositions
                        .record_lowering(surface, &kernel)?;
                }
            }
        }
        let path_tactics = lower_certified_frame_path_tactics(
            &mut construction_replay,
            &execution_state.state,
            &available,
            context.parsed_function.parameters(),
            context.arguments,
            context.predicate_environment,
            context.click_function_environment,
            &path_derivations,
        )
        .map_err(|error| {
            self.step_error(format!(
                "smart frame candidate construction failed: could not lower contextual frame plan: {}",
                error.message()
            ))
        })?;
        // A compatibility root created after a legacy branch owns the
        // outcomes but not the branch Proof that partitions them. It may
        // still check one plan shared by every path; a path-dependent plan
        // declines here instead of inventing missing branch lineage.
        contextual_frame_plan(skeleton, path_tactics, path_independent_only).map_err(|message| {
            self.step_error(format!(
                "smart frame candidate construction failed: {message}"
            ))
        })
    }

    /// Reports whether a source-owned terminal frame can advance this exact
    /// checked Proof. This is a capability query only; a false result leaves
    /// the proof unchanged so a larger transactional Proof attempt can
    /// decline without publishing a partial transition.
    pub(super) fn supports_checked_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        self.supports_checked_execution_frame_using(region, premises)
    }

    /// Applies one source-attributed simple step to this Proof. The source
    /// coordinates schedule already-checked ordered outcome work; they grant
    /// no additional semantic authority.
    pub(super) fn apply_step_at(
        &self,
        step: SimpleProofStep,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )
    }

    /// Searches for a terminal frame candidate and submits the selected
    /// Surface-operation plan directly to this Proof. Successful search returns
    /// the already-checked descendant; it does not export outcomes or replay
    /// the candidate through a second semantic representation.
    pub(super) fn try_smart_frame_at(
        &self,
        region: Option<&CodeRegionRef>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(region) = region {
            let step = SimpleProofStep::FrameUsing {
                region: Some(region.clone()),
                premises: Vec::new(),
            };
            return self
                .apply_step_at(step, tactic_index, source_index)
                .map(Some);
        }
        if matches!(
            self.focused_goal(),
            Some(Goal::Frontier(FrontierGoal {
                selection: EffectGoalSelection::None,
                ..
            }))
        ) {
            return Ok(None);
        }
        let step = SimpleProofStep::FrameUsing {
            region: None,
            premises: Vec::new(),
        };
        match self.apply_step_at(step, tactic_index, source_index) {
            Ok(framed) => return Ok(Some(framed)),
            Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
            Err(_) => {}
        }
        // If the exact empty operation cannot prove the selected effect, use
        // contextual search to select explicit premises and leading haves.
        let Some(candidate) = self.select_contextual_frame_candidate()? else {
            return Ok(None);
        };
        let origin = Some(ProofStepOrigin {
            tactic_index,
            source_index,
        });
        match self.apply_contextual_frame_plan(&candidate, origin) {
            Ok(checked) => Ok(Some(checked)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    /// Selects exact premises for a smart loop structural frame from facts
    /// indexed under C names used by that loop body. Candidate work is bounded
    /// by the affected source operation and its relevant indexed facts; no
    /// ambient fact scan or semantic replay participates.
    pub(super) fn try_smart_loop_effect_frame_at(
        &self,
        body: &CStatement,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let execution = self.execution().ok_or_else(|| {
            self.step_error("smart loop framing requires an execution-frontier Proof")
        })?;
        execution.replay.loop_effect_goal.as_ref().ok_or_else(|| {
            self.step_error("smart loop framing requires a structural effect goal")
        })?;
        let mut dependency_names = BTreeSet::new();
        collect_statement_variable_names(body, &mut dependency_names);
        let mut candidates = BTreeSet::new();
        for name in dependency_names {
            for kernel in execution
                .replay
                .surface_propositions
                .current_c_variable_kernel_facts(&name)
            {
                if self
                    .facts()
                    .replay_available_across_effects(kernel, &execution.replay.effect_facts)
                {
                    candidates.insert(kernel.clone());
                }
            }
        }
        let mut premises = Vec::with_capacity(candidates.len());
        #[cfg(test)]
        SMART_LOOP_EFFECT_FRAME_CANDIDATES.with(|count| count.set(count.get() + candidates.len()));
        for kernel in candidates {
            let Some(surface) = self.loop_effect_surface_premise(&kernel) else {
                continue;
            };
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }
        let selected = SimpleProofStep::FrameUsing {
            region: None,
            premises,
        };
        match self.apply_step_at(selected, tactic_index, source_index) {
            Ok(checked) => Ok(Some(checked)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    fn loop_effect_surface_premise(&self, kernel: &Proposition) -> Option<ClickProposition> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let execution = self.execution()?;
        let matches = |surface: &ClickProposition| {
            let lowered = execution
                .replay
                .surface_propositions
                .available_kernel_matching(surface, |candidate| {
                    self.facts()
                        .replay_available_across_effects(candidate, &execution.replay.effect_facts)
                })
                .cloned()
                .or_else(|| {
                    self.lower_surface_proposition_direct(surface, "smart loop frame premise")
                        .ok()
                });
            lowered.is_some_and(|lowered| {
                lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)
            })
        };
        if let Some(surface) = execution
            .replay
            .surface_propositions
            .surfaces(kernel)
            .find(|surface| matches(surface))
        {
            return Some(surface.clone());
        }
        let surface = synthesize_surface_proposition(
            kernel,
            context.parsed_function.parameters(),
            context.arguments,
            &execution.state,
        )?;
        matches(&surface).then_some(surface)
    }

    // Each primitive rule stays outlined so adding a rule-local proposition
    // payload cannot enlarge every `apply_step` dispatch frame. This is part
    // of the expansion replay stack budget documented in testing-click.md.
    #[inline(never)]
    fn apply_assumption(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`assumption` requires a proposition goal")?;
        let available = match self.context.as_ref() {
            ProofContext::Point(_) => {
                self.facts().pure_replay_available(goal) || normalizes_context_free(goal)
            }
            // A judgment stated at a function outcome closes with the same
            // point-level replay availability its legacy point root used.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                self.facts().pure_replay_available(goal) || normalizes_context_free(goal)
            }
            ProofContext::Pure(_) | ProofContext::Execution(_) => self.facts().contains(goal),
        };
        if !available {
            return Err(self
                .step_error("`assumption` requires the exact current goal as an available fact"));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    fn apply_normalize(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`normalize` requires a proposition goal")?;
        if !normalizes_context_free(goal) {
            return Err(self.step_error("`normalize` goal did not normalize to true"));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    fn apply_intro(&self) -> Result<ProofState, ClickError> {
        let goal = self
            .proposition_goal("`intro` requires a proposition goal")?
            .clone();
        let mut surface_bindings = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => goal.surface_bindings.clone(),
            _ => PersistentMap::default(),
        };
        let (goal, introduced, surface_goal) = match goal {
            Proposition::Implies(antecedent, consequent) => (
                *consequent,
                Some(*antecedent),
                match self.surface_goal() {
                    Some(ClickProposition::Implies(_, consequent)) => {
                        Some(consequent.as_ref().clone())
                    }
                    _ => None,
                },
            ),
            Proposition::ForAll { var, body, .. } => {
                let surface_goal = match self.surface_goal() {
                    Some(ClickProposition::ForAll { name, body, .. }) => {
                        surface_bindings = surface_bindings.with_inserted(
                            name.clone(),
                            ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                                Bitvector32Term::Variable(var),
                            ))),
                        );
                        Some(body.as_ref().clone())
                    }
                    _ => None,
                };
                (*body, None, surface_goal)
            }
            Proposition::Not(body) => (
                Proposition::ConditionIs(ConditionTerm::Constant(false), true),
                Some(*body),
                None,
            ),
            other => {
                return Err(self.step_error(format!(
                    "`intro` requires an implication, negation, or universal goal, got {other:?}"
                )));
            }
        };
        let mut facts = self.facts().clone();
        let added_facts = introduced.into_iter().collect::<Vec<_>>();
        for fact in &added_facts {
            facts = facts.with_fact(fact.clone());
        }
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(self.focused, {
                let context = self.refined_context(facts);
                let mut refined = self.refined_proposition(context, goal, surface_goal);
                let Goal::Proposition(refined_goal) = &mut refined else {
                    unreachable!("intro always refines a proposition goal")
                };
                refined_goal.surface_bindings = surface_bindings;
                refined
            }),
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
        })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    fn apply_split(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`split` requires a proposition goal")?;
        let Proposition::And(left, right) = goal else {
            return Err(
                self.step_error(format!("`split` requires a conjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(left) || !self.facts().contains(right) {
            return Err(self.step_error(format!(
                "`split` requires both conjuncts as exact facts: {left:?} and {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    fn apply_left(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`left` requires a proposition goal")?;
        let Proposition::Or(left, _) = goal else {
            return Err(
                self.step_error(format!("`left` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(left)
            && !condition_polarity_forms(left)
                .iter()
                .any(|form| self.facts().contains(form))
        {
            return Err(self.step_error(format!(
                "`left` requires its selected disjunct as an exact fact: {left:?}"
            )));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    fn apply_right(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`right` requires a proposition goal")?;
        let Proposition::Or(_, right) = goal else {
            return Err(
                self.step_error(format!("`right` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(right)
            && !condition_polarity_forms(right)
                .iter()
                .any(|form| self.facts().contains(form))
        {
            return Err(self.step_error(format!(
                "`right` requires its selected disjunct as an exact fact: {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    // Preserve the rule/dispatcher frame boundary described above; instance
    // materialization is local to this rule.
    #[inline(never)]
    fn apply_enumerate(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`enumerate` requires a proposition goal")?;
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Err(
                self.step_error("`enumerate` requires a universal goal with constant bounds")
            );
        };
        for (_, instance) in instances {
            if !normalizes_context_free(&instance) && !self.facts().contains(&instance) {
                return Err(self.step_error(
                    "`enumerate` requires each in-range instance as an exact available fact",
                ));
            }
        }
        Ok(self.closed_state())
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

    /// Splits the focused proposition goal into two labeled sibling case
    /// goals inside this same proof state.
    ///
    /// This is the in-`Proof` form of `cases`: the parent obligation's id is
    /// retired by the split, each arm owns the same claim under its exact
    /// disjunct in its own path-local context, and both siblings coexist in
    /// one goal collection — arms are proven by focusing each recorded id in
    /// turn on one lineage. The split marker node records this split
    /// instance; the join accepts only derivations that pass through it.
    pub(super) fn split_focused_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, SplitId, [GoalId; 2]), ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`cases` follows a completed proof"));
        }
        let Some(Goal::Proposition(goal)) = self.focused_goal() else {
            return Err(self.step_error("`cases` requires a proposition goal"));
        };
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        if !self.facts().contains(&kernel) {
            return Err(self.step_error(format!(
                "`cases` requires its exact disjunction as an available fact: {kernel:?}"
            )));
        }
        let Proposition::Or(left, right) = kernel else {
            return Err(self.step_error(format!("`cases` requires a disjunction, got {kernel:?}")));
        };
        let arm = |disjunct: Proposition| {
            Goal::Proposition(PropositionGoal {
                kernel: goal.kernel.clone(),
                surface: goal.surface.clone(),
                surface_bindings: goal.surface_bindings.clone(),
                context: GoalContext {
                    facts: goal.context.facts.with_fact(disjunct),
                    unfolded_predicates: goal.context.unfolded_predicates.clone(),
                    execution: goal.context.execution.clone(),
                },
                outcome: goal.outcome.clone(),
            })
        };
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [arm(*left), arm(*right)]);
        Ok((
            Self {
                context: self.context.clone(),
                state: Arc::new(ProofState {
                    locals: self.state.locals.clone(),
                    goals,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                }),
                // The marker records the split instance in provenance; its
                // identity is what the join verifies (identity rule 3).
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused: self.focused,
                    depth: self.node.depth,
                }),
                focused: ids[0],
            },
            split,
            ids,
        ))
    }

    /// Splits the focused proposition goal under a condition and its exact
    /// surface negation inside this same proof state: the in-`Proof` form of
    /// proof `if`. Unlike `cases`, the condition need not be an available
    /// fact beforehand.
    pub(super) fn split_focused_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, SplitId, [GoalId; 2]), ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`if` follows a completed proof"));
        }
        let Some(Goal::Proposition(goal)) = self.focused_goal() else {
            return Err(self.step_error("proof `if` requires a proposition goal"));
        };
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let arm = |fact: Proposition| {
            Goal::Proposition(PropositionGoal {
                kernel: goal.kernel.clone(),
                surface: goal.surface.clone(),
                surface_bindings: goal.surface_bindings.clone(),
                context: GoalContext {
                    facts: goal.context.facts.with_fact(fact),
                    unfolded_predicates: goal.context.unfolded_predicates.clone(),
                    execution: goal.context.execution.clone(),
                },
                outcome: goal.outcome.clone(),
            })
        };
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [arm(then_fact), arm(else_fact)]);
        Ok((
            Self {
                context: self.context.clone(),
                state: Arc::new(ProofState {
                    locals: self.state.locals.clone(),
                    goals,
                    added_facts: Arc::new(Vec::new()),
                    checked_facts: Arc::new(Vec::new()),
                }),
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused: self.focused,
                    depth: self.node.depth,
                }),
                focused: ids[0],
            },
            split,
            ids,
        ))
    }

    /// Enters the exhaustive operational partition produced by the
    /// immediately preceding statement step. The proof `if` introduces no
    /// hypothesis of its own: both Surface polarities must lower to the exact
    /// condition already certified for the two successor frontiers.
    pub(super) fn enter_statement_successor_if(
        &self,
        condition: &ClickProposition,
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(partition) = self
            .execution()
            .and_then(|execution| execution.last_step_delta.statement_partition.clone())
        else {
            return Ok(None);
        };
        if self.focused != partition.ids[0]
            || !matches!(
                self.node.step.as_deref(),
                Some(SimpleProofStep::Step | SimpleProofStep::StepUsing(_))
            )
        {
            return Err(self
                .step_error("statement-successor `if` must immediately follow its checked step"));
        }
        let then_fact = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let expected_then = Proposition::ConditionIs(partition.condition.clone(), true);
        if !path_condition_equivalent(&then_fact, &expected_then) {
            return Err(self.step_error(format!(
                "proof `if` condition does not name the preceding statement's certified partition: expected {expected_then:?}, got {then_fact:?}"
            )));
        }
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        // Lower both polarities against one semantic snapshot. Independent
        // lowering in the sibling successor can allocate different fresh
        // names for the same snapshot-qualified load, making an exact
        // certified partition appear different across its two arms.
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let expected_else = Proposition::ConditionIs(partition.condition.clone(), false);
        if !path_condition_equivalent(&else_fact, &expected_else) {
            return Err(self.step_error(format!(
                "proof `if` negation does not name the preceding statement's certified partition: expected {expected_else:?}, got {else_fact:?}"
            )));
        }

        let successor = Self {
            context: self.context.clone(),
            state: self.state.clone(),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.node.focused,
                depth: self.node.depth,
            }),
            focused: partition.ids[0],
        };
        let record = ExecutionProofCaseSplit {
            marker: successor.checkpoint(),
            split: partition.split,
            ids: partition.ids,
            surface_condition: condition.clone(),
            base_facts: partition.base_facts.clone(),
            base_executions: partition.base_executions.clone(),
            path_facts: partition.path_facts.clone(),
            common_facts: partition.common_facts.clone(),
            parent_unfolds: partition.parent_unfolds.clone(),
            parent_execution: partition.parent_execution.clone(),
            execution_start_state: partition.execution_start_state.clone(),
            initial_continuation_depth: partition.initial_continuation_depth,
        };
        Ok(Some((successor, record)))
    }

    /// Splits a proof path condition that exactly names the current C `if`
    /// and applies each arm's leading source step as a checked `StepUsing`
    /// operation on that focused Proof. Smart entries arrive with the same
    /// explicit premises selected by their caller. The returned arms remain
    /// proof cases, so their source scopes may continue through the C join;
    /// only the branch-entry transition is selected here.
    pub(super) fn try_split_source_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, usize, Vec<ClickProposition>); 2],
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        // A preceding call or other multi-successor statement already owns a
        // certified partition. Its bounded product requires explicit source
        // evidence to exclude parent lanes; a fresh proof-case assumption
        // must not bypass that checked adapter merely because the following
        // C statement uses the same condition.
        if execution.last_step_delta.statement_partition.is_some() {
            return Ok(None);
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let statement_index = execution.replay.frontier.next_statement_index;
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &execution.replay,
            &execution.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "source proof `if`",
        )?;
        let CStatement::If {
            condition: c_condition,
            ..
        } = statement
        else {
            return Ok(None);
        };
        let source_fact = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let c_surface = surface_c_condition(&c_condition);
        let c_fact = self.lower_surface_proposition(&c_surface, "current C `if` condition")?;
        if !path_condition_equivalent(&source_fact, &c_fact) {
            return Ok(None);
        }

        let (split, mut record) = self.split_focused_execution_if(condition.clone())?;
        record.surface_condition = surface_with_source_site(
            &c_surface,
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let mut advanced = split;
        for (arm_index, take_then) in [(0usize, true), (1usize, false)] {
            let (tactic_index, source_index, premises) = &arm_steps[arm_index];
            advanced = advanced
                .focus_execution_if_arm(&record, take_then)?
                .apply_step_at(
                    SimpleProofStep::StepUsing(premises.clone()),
                    *tactic_index,
                    *source_index,
                )?;
        }
        Ok(Some((advanced, record)))
    }

    /// Tries the one bounded product needed when a proof-level condition does
    /// not name the immediately preceding statement partition. Each logical
    /// polarity is checked against both certified statement successors while
    /// crossing exactly the following C `if`. The speculative product is
    /// accepted only when each polarity immediately has exactly one survivor;
    /// no multi-frontier family is ever published to the proof state.
    pub(super) fn try_collapse_statement_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, Vec<ClickProposition>); 2],
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(partition) = self
            .execution()
            .and_then(|execution| execution.last_step_delta.statement_partition.clone())
        else {
            return Ok(None);
        };
        if self.focused != partition.ids[0]
            || !matches!(
                self.node.step.as_deref(),
                Some(SimpleProofStep::Step | SimpleProofStep::StepUsing(_))
            )
        {
            return Ok(None);
        }

        // The exact-partition adapter is both cheaper and more informative.
        // Leave that case to `enter_statement_successor_if`.
        let first_then = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let expected_then = Proposition::ConditionIs(partition.condition.clone(), true);
        if path_condition_equivalent(&first_then, &expected_then) {
            return Ok(None);
        }

        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            return Ok(None);
        };
        let selection = frontier.selection;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        for execution in &partition.base_executions {
            let statement_index = execution.replay.frontier.next_statement_index;
            let Some(region) = execution.replay.source_layout.statement(statement_index) else {
                return Ok(None);
            };
            if !matches!(region.kind, SourceStatementKind::If { .. }) {
                return Ok(None);
            }
        }

        struct Survivor {
            base_facts: ProofFacts,
            base_execution: Arc<ExecutionProofState>,
            path_fact: Proposition,
            checked: CheckedStatementStep,
        }

        enum LaneDecision {
            Excluded,
            Survives(Proposition),
        }

        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let mut survivors: [Option<Survivor>; 2] = [None, None];
        for logical_arm in 0..2 {
            let take_then = logical_arm == 0;
            let surface_fact = if take_then {
                condition.clone()
            } else {
                else_surface.clone()
            };
            let mut survivor = None;
            for parent_arm in 0..2 {
                let focused = self.focus(partition.ids[parent_arm])?;
                let decision = crate::instrumentation::measure_operation(
                    context.function.name(),
                    context.claim_label,
                    "bounded statement-successor exclusion",
                    || -> Result<Option<LaneDecision>, ClickError> {
                        let fact = focused.lower_surface_proposition(
                            &surface_fact,
                            if take_then {
                                "proof `if` condition"
                            } else {
                                "proof `if` negation"
                            },
                        )?;
                        // Exclusion is intentionally bounded by source
                        // evidence. It asks only whether the arm polarity plus
                        // explicitly named premises refute one of this lane's
                        // exact certified partition facts; it never searches
                        // the ambient context for a global contradiction.
                        let mut evidence = Vec::new();
                        for premise in &arm_steps[logical_arm].1 {
                            let lowered = focused.lower_surface_proposition(
                                premise,
                                "bounded statement-successor premise",
                            )?;
                            if !partition.base_facts[parent_arm].contains(&lowered) {
                                return Ok(None);
                            }
                            if !evidence.contains(&lowered) {
                                evidence.push(lowered);
                            }
                        }
                        let premise_context = assumptions_from_propositions(&evidence);
                        if partition.path_facts[parent_arm].iter().any(|path_fact| {
                            fact_conflicts_with_assumptions(path_fact, &premise_context)
                        }) {
                            return Ok(None);
                        }
                        evidence.push(fact.clone());
                        let arm_context = assumptions_from_propositions(&evidence);
                        let arm_refutes_parent =
                            partition.path_facts[parent_arm].iter().any(|path_fact| {
                                fact_conflicts_with_assumptions(path_fact, &arm_context)
                            });
                        evidence.pop();
                        evidence.extend(partition.path_facts[parent_arm].iter().cloned());
                        let parent_context = assumptions_from_propositions(&evidence);
                        let parent_refutes_arm =
                            fact_conflicts_with_assumptions(&fact, &parent_context);
                        Ok(Some(if arm_refutes_parent || parent_refutes_arm {
                            LaneDecision::Excluded
                        } else {
                            LaneDecision::Survives(fact)
                        }))
                    },
                )?;
                let Some(decision) = decision else {
                    return Ok(None);
                };
                let LaneDecision::Survives(fact) = decision else {
                    continue;
                };
                let facts = partition.base_facts[parent_arm].with_fact(fact.clone());
                let mut execution = (*partition.base_executions[parent_arm]).clone();
                execution.last_step_delta = ExecutionProofStepDelta::default();
                execution
                    .replay
                    .surface_propositions
                    .record_lowering(&surface_fact, &fact)?;
                execution
                    .replay
                    .case_assumptions
                    .push(ReplayCaseAssumption {
                        tactic_index: context.tactic_index,
                        condition: condition.clone(),
                        value: take_then,
                        fact: Some(fact.clone()),
                        at_function_entry: execution.replay.is_at_function_entry(),
                    });
                let base_execution = Arc::new(execution.clone());
                let mut checked = check_step_using_facts(
                    &mut execution.replay,
                    &mut execution.state,
                    &facts,
                    &arm_steps[logical_arm].1,
                    context.function_block,
                    context.function,
                    context.parsed_function,
                    context.arguments,
                    context.function_environment,
                    context.predicate_environment,
                    context.click_function_environment,
                    context.claim_label,
                    arm_steps[logical_arm].0,
                )?;
                match checked.len() {
                    0 => {}
                    1 if survivor.is_none() => {
                        survivor = Some(Survivor {
                            base_facts: facts,
                            base_execution,
                            path_fact: fact,
                            checked: checked.pop().expect("one successor was checked"),
                        });
                    }
                    // More than one surviving parent lane, or a statement
                    // that itself still branches, did not collapse within
                    // the fixed four-check boundary.
                    _ => return Ok(None),
                }
            }
            let Some(survivor) = survivor else {
                return Ok(None);
            };
            survivors[logical_arm] = Some(survivor);
        }

        let [Some(then_survivor), Some(else_survivor)] = survivors else {
            unreachable!("both logical arms were required above")
        };
        let make_goal = |survivor: &Survivor| {
            let mut execution = (*survivor.base_execution).clone();
            execution.replay = survivor.checked.replay.clone();
            execution.state = survivor.checked.state.clone().into();
            Goal::Frontier(FrontierGoal {
                selection,
                context: GoalContext {
                    facts: survivor.checked.facts.clone(),
                    unfolded_predicates: partition.parent_unfolds.clone(),
                    execution: Some(Arc::new(execution)),
                },
            })
        };
        let goals = self
            .state
            .goals
            .replace_at(partition.ids[0], make_goal(&then_survivor))
            .replace_at(partition.ids[1], make_goal(&else_survivor));
        let marker_node = Arc::new(ProofNode {
            parent: Some(self.node.clone()),
            step: None,
            focused: self.focused,
            depth: self.node.depth,
        });
        let then_node = Arc::new(ProofNode {
            parent: Some(marker_node.clone()),
            step: Some(Arc::new(SimpleProofStep::StepUsing(arm_steps[0].1.clone()))),
            focused: partition.ids[0],
            depth: marker_node.depth + 1,
        });
        let else_node = Arc::new(ProofNode {
            parent: Some(then_node),
            step: Some(Arc::new(SimpleProofStep::StepUsing(arm_steps[1].1.clone()))),
            focused: partition.ids[1],
            depth: marker_node.depth + 2,
        });
        let then_path = vec![then_survivor.path_fact.clone()];
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(then_path.clone()),
                checked_facts: Arc::new(then_path.clone()),
            }),
            node: else_node,
            focused: partition.ids[0],
        };
        let record = ExecutionProofCaseSplit {
            marker: ProofCheckpoint {
                context: self.context.clone(),
                node: marker_node,
            },
            split: partition.split,
            ids: partition.ids,
            surface_condition: condition.clone(),
            base_facts: [then_survivor.base_facts, else_survivor.base_facts],
            base_executions: [then_survivor.base_execution, else_survivor.base_execution],
            path_facts: [then_path, vec![else_survivor.path_fact]],
            common_facts: partition.common_facts.clone(),
            parent_unfolds: partition.parent_unfolds.clone(),
            parent_execution: partition.parent_execution.clone(),
            execution_start_state: partition.execution_start_state.clone(),
            initial_continuation_depth: partition.initial_continuation_depth,
        };
        Ok(Some((successor, record)))
    }

    /// Splits one retained execution frontier under an exhaustive proof-level
    /// condition. Both arms share the already-checked C state and receive only
    /// their respective logical polarity; subsequent statement steps remain
    /// independently checked on each sibling.
    pub(super) fn split_focused_execution_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        self.require_execution_frontier("proof `if`")?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above")
        };
        let parent_execution = frontier
            .context
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("an execution frontier has an execution context")
        };
        let at_function_entry = parent_execution.replay.is_at_function_entry();
        let arm = |surface_fact: ClickProposition, fact: Proposition, value: bool| {
            let facts = frontier.context.facts.with_fact(fact.clone());
            let mut execution = (*parent_execution).clone();
            execution
                .replay
                .surface_propositions
                .record_lowering(&surface_fact, &fact)?;
            execution
                .replay
                .case_assumptions
                .push(ReplayCaseAssumption {
                    tactic_index: context.tactic_index,
                    condition: condition.clone(),
                    value,
                    fact: Some(fact.clone()),
                    at_function_entry,
                });
            Ok((
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts: facts.clone(),
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(Arc::new(execution.clone())),
                    },
                }),
                facts,
                vec![fact],
                Arc::new(execution),
            ))
        };
        let (then_goal, then_facts, then_path, then_execution) =
            arm(condition.clone(), then_fact, true)?;
        let (else_goal, else_facts, else_path, else_execution) =
            arm(else_surface, else_fact, false)?;
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [then_goal, else_goal]);
        let first_path = then_path.clone();
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(first_path.clone()),
                checked_facts: Arc::new(first_path),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: ids[0],
        };
        let record = ExecutionProofCaseSplit {
            marker: successor.checkpoint(),
            split,
            ids,
            surface_condition: condition,
            base_facts: [then_facts, else_facts],
            base_executions: [then_execution, else_execution],
            path_facts: [then_path, else_path],
            common_facts: frontier.context.facts.clone(),
            parent_unfolds: frontier.context.unfolded_predicates.clone(),
            parent_execution: parent_execution.clone(),
            execution_start_state: parent_execution
                .replay
                .execution_start_state(&parent_execution.state)
                .clone(),
            initial_continuation_depth: parent_execution.replay.frontier.continuations.len(),
        };
        Ok((successor, record))
    }

    /// Splits one retained execution frontier under the two exact disjuncts
    /// of an available proposition. The disjunction is checked once at the
    /// split; each sibling receives only its own disjunct in its persistent
    /// fact context, and no semantic state is exported to a replay cursor.
    pub(super) fn split_focused_execution_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, ExecutionLogicalCasesSplit<'a>), ClickError> {
        self.require_execution_frontier("`cases`")?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above")
        };
        let parent_execution = frontier
            .context
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let lowered = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        if !frontier.context.facts.contains(&lowered) {
            return Err(self.step_error(format!(
                "`cases` requires its exact disjunction as an available fact: {lowered:?}"
            )));
        }
        let Proposition::Or(left, right) = lowered else {
            return Err(self.step_error(format!("`cases` requires a disjunction, got {lowered:?}")));
        };
        let arm = |disjunct: Proposition| {
            let facts = frontier.context.facts.with_fact(disjunct.clone());
            (
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts,
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(parent_execution.clone()),
                    },
                }),
                vec![disjunct],
            )
        };
        let (left_goal, left_path) = arm(*left);
        let (right_goal, right_path) = arm(*right);
        let (split, ids, goals) = self
            .state
            .goals
            .split_at(self.focused, [left_goal, right_goal]);
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(left_path.clone()),
                checked_facts: Arc::new(left_path.clone()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: ids[0],
        };
        let record = ExecutionLogicalCasesSplit {
            marker: successor.checkpoint(),
            split,
            ids,
            path_facts: [left_path, right_path],
        };
        Ok((successor, record))
    }

    /// Focuses one arm of a logical execution-frontier `cases` split. The
    /// arm's exact disjunct is re-presented only as this focused operation's
    /// local fact delta.
    pub(super) fn focus_execution_cases_arm(
        &self,
        record: &ExecutionLogicalCasesSplit<'a>,
        take_left: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_left);
        let mut focused = self.focus(record.ids[arm_index])?;
        let path_facts = record.path_facts[arm_index].clone();
        focused.state = Arc::new(ProofState {
            locals: focused.state.locals.clone(),
            goals: focused.state.goals.clone(),
            added_facts: Arc::new(path_facts.clone()),
            checked_facts: Arc::new(path_facts),
        });
        Ok(focused)
    }

    /// Applies one recursively driven logical `cases` operation over an
    /// execution frontier. Both callbacks must retire their sibling goals;
    /// the returned node retains one structured `Cases` provenance step.
    pub(super) fn apply_execution_cases_with<Left, Right>(
        self,
        disjunction: ClickProposition,
        apply_left: Left,
        apply_right: Right,
    ) -> Result<Self, ClickError>
    where
        Left: FnOnce(Self) -> Result<Self, ClickError>,
        Right: FnOnce(Self) -> Result<Self, ClickError>,
    {
        let (split, record) = self.split_focused_execution_cases(disjunction.clone())?;
        let left_done = apply_left(split.focus_execution_cases_arm(&record, true)?)?;
        let right_done = apply_right(left_done.focus_execution_cases_arm(&record, false)?)?;
        right_done.join_focused_cases(&record.marker, record.split, record.ids, disjunction)
    }

    /// Applies one recursively driven proof-level execution `if` as an
    /// audited sibling-goal operation. Each callback must retire exactly its
    /// selected arm, either with terminal checked steps or another invocation
    /// of this operation. The returned node retains the structured `If`
    /// provenance directly on this Proof lineage.
    pub(super) fn apply_execution_if_with<Then, Else>(
        self,
        condition: ClickProposition,
        apply_then: Then,
        apply_else: Else,
    ) -> Result<Self, ClickError>
    where
        Then: FnOnce(Self) -> Result<Self, ClickError>,
        Else: FnOnce(Self) -> Result<Self, ClickError>,
    {
        let (split, record) = self.split_focused_execution_if(condition.clone())?;
        let then_done = apply_then(split.focus_execution_if_arm(&record, true)?)?;
        let else_done = apply_else(then_done.focus_execution_if_arm(&record, false)?)?;
        else_done.join_focused_if(&record.marker, record.split, record.ids, condition)
    }

    /// Joins a completed in-`Proof` `if` split with one structured `If`
    /// step, under the same rules as [`Self::join_focused_cases`].
    pub(super) fn join_focused_if(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [GoalId; 2],
        condition: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| SimpleProofStep::If {
            condition,
            then_proof: Box::new(left),
            else_proof: Box::new(right),
        })
    }

    /// Joins a completed in-`Proof` case split: both recorded sibling goals
    /// must be discharged, the derivation must pass through the split's
    /// exact marker, and the retained certificate embeds each arm's steps
    /// partitioned by the per-step goal attribution recorded when they were
    /// applied — never inferred from final states.
    pub(super) fn join_focused_cases(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [GoalId; 2],
        disjunction: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| SimpleProofStep::Cases {
            disjunction,
            left_proof: Box::new(left),
            right_proof: Box::new(right),
        })
    }

    /// Splits the steps recorded since `marker` into per-arm certificates by
    /// the goal attribution stamped on each node when it was applied. The
    /// derivation must pass through the split's exact marker (foreign splits
    /// of the same root collide numerically but fail pointer identity), and
    /// every step in the region must be attributed to one of the two
    /// recorded arms.
    fn partition_steps_since(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [GoalId; 2],
    ) -> Result<[Vec<SimpleProofStep>; 2], ClickError> {
        let mut left_steps = Vec::new();
        let mut right_steps = Vec::new();
        let mut node = Some(self.node.clone());
        loop {
            let Some(current) = node else {
                return Err(self.step_error(format!(
                    "cannot join: the derivation did not pass through split {split:?}"
                )));
            };
            if Arc::ptr_eq(&current, &marker.node) {
                break;
            }
            if let Some(step) = &current.step {
                if current.focused == ids[0] {
                    left_steps.push(step.as_ref().clone());
                } else if current.focused == ids[1] {
                    right_steps.push(step.as_ref().clone());
                } else {
                    return Err(self.step_error(format!(
                        "cannot join: a step was attributed outside split {split:?}"
                    )));
                }
            }
            node = current.parent.clone();
        }
        left_steps.reverse();
        right_steps.reverse();
        Ok([left_steps, right_steps])
    }

    fn join_focused_branch(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [GoalId; 2],
        step: impl FnOnce(ProofCertificate, ProofCertificate) -> SimpleProofStep,
    ) -> Result<Self, ClickError> {
        for (name, id) in [("left", ids[0]), ("right", ids[1])] {
            if self.state.goals.get(id).is_some() {
                return Err(
                    self.step_error(format!("cannot join `cases`: {name} arm is incomplete"))
                );
            }
        }
        let [left_steps, right_steps] = self.partition_steps_since(marker, split, ids)?;
        let parent = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `cases`: the split marker lost its root")
        })?;
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: self.state.goals.clone(),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(parent.clone()),
                step: Some(Arc::new(step(
                    ProofCertificate::from_steps(left_steps),
                    ProofCertificate::from_steps(right_steps),
                ))),
                focused: marker.node.focused,
                depth: parent.depth + 1,
            }),
            focused: marker.node.focused,
        })
    }

    /// Partitions an already-checked terminal execution by one proof-level
    /// condition. Every owned outcome must decide exactly one polarity; no
    /// path may be copied into both arms or silently discarded.
    /// Partitions an already-checked terminal execution by one proof-level
    /// condition into two sibling frontier goals inside this proof. Every
    /// owned outcome must decide exactly one polarity; no path may be
    /// copied into both arms or silently discarded. Unlike a proposition
    /// sibling split, the arms retain execution-frontier goals owning
    /// disjoint subsets of the checked execution, so branch-local facts
    /// justify terminal simple steps without being exposed to incompatible
    /// outcomes.
    fn split_focused_outcome_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, OutcomeSplit<'a>), ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("execution outcome `if` follows a completed proof"));
        }
        let ProofContext::Execution(_) = self.context.as_ref() else {
            return Err(self.step_error("execution outcome `if` requires an execution proof"));
        };
        self.require_execution_frontier("execution outcome `if`")?;
        let root_execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution outcome `if` lost its semantic frontier"))?;
        if !root_execution.replay.is_at_function_exit() {
            return Err(self.step_error("execution outcome `if` requires function exit"));
        }
        let checked = root_execution.replay.execution().ok_or_else(|| {
            self.step_error("execution outcome `if` has no checked execution paths")
        })?;
        let then_fact =
            self.lower_surface_proposition(&condition, "execution outcome condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact =
            self.lower_surface_proposition(&else_surface, "execution outcome negation")?;
        let shared_facts = self.facts().to_vec();
        type OutcomePath = (
            CFunctionOutcome,
            Vec<ExecutionPureFact>,
            Vec<ProofObligation>,
        );
        let mut partition_paths: [Vec<OutcomePath>; 2] = [Vec::new(), Vec::new()];
        let mut common_path_facts: [Option<Vec<Proposition>>; 2] = [None, None];

        for (path_index, path) in checked.paths().iter().enumerate() {
            let mut available = shared_facts.clone();
            let path_facts = path
                .facts()
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            available.extend(path_facts.iter().cloned());
            let assumptions = assumptions_from_propositions(&available);
            let selects_then =
                exact_fact_is_available(&then_fact, &available) || assumptions.proves(&then_fact);
            let selects_else = exact_fact_is_available(&else_fact, &available)
                || assumptions.proves(&else_fact)
                || fact_conflicts_with_assumptions(&then_fact, &assumptions);
            let arm_index = match (selects_then, selects_else) {
                (true, false) => 0,
                (false, true) => 1,
                (false, false) => {
                    return Err(self.step_error(format!(
                        "execution path {path_index} does not decide outcome branch `{}`",
                        describe_click_proposition(&condition)
                    )));
                }
                (true, true) => {
                    return Err(self.step_error(format!(
                        "execution path {path_index} proves both sides of outcome branch `{}`",
                        describe_click_proposition(&condition)
                    )));
                }
            };
            match &mut common_path_facts[arm_index] {
                Some(common) => common.retain(|fact| path_facts.contains(fact)),
                slot @ None => *slot = Some(path_facts),
            }
            partition_paths[arm_index].push((
                path.outcome().clone(),
                path.execution_facts(),
                path.obligations().to_vec(),
            ));
        }
        if partition_paths.iter().any(Vec::is_empty) {
            return Err(self.step_error(
                "execution outcome `if` requires at least one checked path in each arm",
            ));
        }

        let execution_state = checked.state().clone();
        let function = checked.function().clone();
        let arguments = checked.arguments().to_vec();
        let polarity_facts = [then_fact, else_fact];
        let polarity_surfaces = [condition.clone(), else_surface];
        let Some(Goal::Frontier(parent)) = self.focused_goal() else {
            unreachable!("the execution frontier requirement was checked above")
        };
        let ProofContext::Execution(execution_context) = self.context.as_ref() else {
            unreachable!("the execution context requirement was checked above")
        };
        let expected_effects = self.selected_effect_indices(execution_context)?;
        let selection = parent.selection;
        let parent_facts = parent.context.facts.clone();
        let parent_unfolds = parent.context.unfolded_predicates.clone();
        let parent_execution = parent
            .context
            .execution
            .clone()
            .expect("the execution frontier owns its semantic state");
        let split = SplitId(self.state.goals.next_id);
        let ids = [
            GoalId(self.state.goals.next_id + 1),
            GoalId(self.state.goals.next_id + 2),
        ];
        let mut open = self.state.goals.open.without_key(&self.focused);
        let mut path_facts: [Vec<Proposition>; 2] = [Vec::new(), Vec::new()];
        for arm_index in 0..2 {
            let mut execution = root_execution.clone();
            let paths = std::mem::take(&mut partition_paths[arm_index]);
            execution.replay.frontier.point = ProofExecutionPoint::FunctionExit {
                execution: c_function_execution_candidates_from_outcomes(
                    execution_state.clone(),
                    function.clone(),
                    arguments.clone(),
                    paths,
                ),
            };
            execution.last_step_delta = ExecutionProofStepDelta::default();
            execution
                .replay
                .surface_propositions
                .record_lowering(&polarity_surfaces[arm_index], &polarity_facts[arm_index])?;

            let mut facts = parent_facts.clone();
            let mut added_facts = Vec::new();
            for fact in std::iter::once(&polarity_facts[arm_index])
                .chain(common_path_facts[arm_index].as_ref().into_iter().flatten())
            {
                if !facts.contains(fact) {
                    facts = facts.with_fact(fact.clone());
                    added_facts.push(fact.clone());
                }
            }
            path_facts[arm_index] = added_facts;
            open = open.with_inserted(
                ids[arm_index],
                Goal::Frontier(FrontierGoal {
                    selection,
                    context: GoalContext {
                        facts,
                        unfolded_predicates: parent_unfolds.clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
            );
        }
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: ProofGoals {
                    open,
                    next_id: self.state.goals.next_id + 3,
                },
                added_facts: Arc::new(path_facts[0].clone()),
                checked_facts: Arc::new(path_facts[0].clone()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: ids[0],
        };
        let record = OutcomeSplit {
            marker: successor.checkpoint(),
            split,
            ids,
            condition,
            expected_effects,
            path_facts,
            parent_facts,
            parent_unfolds,
            parent_execution,
            root_post_execution_count: root_execution.replay.post_execution_tactics.len(),
        };
        Ok((successor, record))
    }

    /// Focuses one recorded outcome-partition arm and installs that arm's
    /// entry fact delta as the proof's delta, as `focus_split_arm` does for
    /// C-branch siblings.
    fn focus_outcome_arm(
        &self,
        record: &OutcomeSplit<'a>,
        arm_index: usize,
    ) -> Result<Self, ClickError> {
        let mut focused = self.focus(record.ids[arm_index])?;
        let delta = record.path_facts[arm_index].clone();
        focused.state = Arc::new(ProofState {
            locals: focused.state.locals.clone(),
            goals: focused.state.goals.clone(),
            added_facts: Arc::new(delta.clone()),
            checked_facts: Arc::new(delta),
        });
        Ok(focused)
    }

    /// Joins two exhaustive terminal outcome partitions after both sibling
    /// arms checked the same effect selection. Each arm may retain
    /// different simple evidence, but ordered finalization receives one
    /// authority and therefore performs the resource transition once per
    /// original path. The parent obligation resumes under its original id
    /// with its effect goal closed.
    fn join_focused_outcome_if(&self, record: &OutcomeSplit<'a>) -> Result<Self, ClickError> {
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, record.ids)?;
        let arm_certificates = [
            ProofCertificate::from_steps(then_steps),
            ProofCertificate::from_steps(else_steps),
        ];
        let mut checked_deferrals = Vec::with_capacity(2);
        for (name, id) in [("then", record.ids[0]), ("else", record.ids[1])] {
            let Some(Goal::Frontier(frontier)) = self.state.goals.get(id) else {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm is not an open execution frontier"
                )));
            };
            if !matches!(frontier.selection, EffectGoalSelection::None) {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not close its effect goal"
                )));
            }
            let execution = frontier.context.execution.as_deref().ok_or_else(|| {
                self.step_error(format!(
                    "execution outcome {name} arm lost its semantic frontier"
                ))
            })?;
            if !execution.replay.is_at_function_exit() {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not remain at function exit"
                )));
            }
            let mut added = execution
                .replay
                .post_execution_tactics
                .iter()
                .skip(record.root_post_execution_count);
            let deferred = added.next().ok_or_else(|| {
                self.step_error(format!(
                    "execution outcome {name} arm retained no checked terminal operation"
                ))
            })?;
            if added.next().is_some() {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm retained more than one terminal operation"
                )));
            }
            let PostExecutionTactic::CheckedFrameUsing { authority, .. } = &deferred.tactic else {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm did not retain checked frame authority"
                )));
            };
            if authority.effect_indices.as_ref() != &record.expected_effects {
                return Err(self.step_error(format!(
                    "execution outcome {name} arm closed a different effect selection"
                )));
            }
            checked_deferrals.push(deferred.clone());
        }
        if checked_deferrals[0].tactic_index != checked_deferrals[1].tactic_index
            || checked_deferrals[0].source_index != checked_deferrals[1].source_index
        {
            return Err(self.step_error(
                "execution outcome arms attribute their frame to different source tactics",
            ));
        }

        let mut execution = (*record.parent_execution).clone();
        execution.replay.defer_checked_post_execution(
            checked_deferrals[0].tactic_index,
            checked_deferrals[0].source_index,
            PostExecutionTactic::CheckedFrameUsing {
                authority: CheckedFrameAuthority::new(record.expected_effects.clone()),
                // The structured node below owns the two exact surface
                // forms. This deferral is semantic authority only.
                region: None,
                premises: Vec::new(),
                surface_tactics: None,
            },
        );
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let parent_goal = record.marker.node.focused;
        let parent_node = record.marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join outcome `if`: the split marker lost its root")
        })?;
        let open = self
            .state
            .goals
            .open
            .without_key(&record.ids[0])
            .without_key(&record.ids[1])
            .with_inserted(
                parent_goal,
                Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    context: GoalContext {
                        facts: record.parent_facts.clone(),
                        unfolded_predicates: record.parent_unfolds.clone(),
                        execution: Some(Arc::new(execution)),
                    },
                }),
            );
        let [then_certificate, else_certificate] = arm_certificates;
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: ProofGoals {
                    open,
                    next_id: self.state.goals.next_id,
                },
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(parent_node.clone()),
                step: Some(Arc::new(SimpleProofStep::If {
                    condition: record.condition.clone(),
                    then_proof: Box::new(then_certificate),
                    else_proof: Box::new(else_certificate),
                })),
                focused: parent_goal,
                depth: parent_node.depth + 1,
            }),
            focused: parent_goal,
        })
    }

    /// Opens a nested proof for one surface proposition. The body has a fresh
    /// provenance root but shares the persistent semantic fact index and
    /// immutable checking context with its enclosing proof.
    ///
    /// A point proof may open `have` either while refining a proposition or
    /// from its initial result frontier. The latter is the audited way for
    /// grouped contract finalization to prove one obligation, publish it as a
    /// checked fact, and then prove a dependent obligation without rebuilding
    /// or mutating an external fact context.
    pub(super) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`have` follows a completed proof"));
        }
        match (self.focused_goal(), self.context.as_ref()) {
            (Some(Goal::Proposition(_) | Goal::FunctionOutcome(_)), _) => {}
            (Some(Goal::Frontier(_)), ProofContext::Point(_) | ProofContext::Execution(_)) => {}
            _ => {
                return Err(self.step_error("`have` requires a proposition or point context"));
            }
        }
        let kernel = self.lower_surface_goal(&proposition, "`have` proposition")?;
        // A post-execution unfold lets a predicate-call `have` prove the
        // predicate through its structural body. Pair that body kernel with
        // the same unfolded Surface view so `intro` retains binder names and
        // subsequent simple steps serialize an independently replayable
        // proof. Joining still publishes the opaque `kernel` named by the
        // enclosing Have step.
        let structural_proposition = if let ClickProposition::PredicateCall { name, .. } =
            &proposition
            && self.focused_goal_unfolds().contains(name)
        {
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::Point(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let active_unfolds = self.focused_goal_unfolds().to_vec();
            unfold_structural_invariant_proposition(
                predicate_environment,
                &proposition,
                &active_unfolds,
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `have` goal: {message}"))
            })?
        } else {
            proposition.clone()
        };
        let body_kernel = self.lower_surface_goal(&structural_proposition, "`have` body")?;
        let mut body_facts = self.facts().with_selected_resource_separation(&body_kernel);
        let selected_surface_separation = match &structural_proposition {
            ClickProposition::Separate { .. } => true,
            ClickProposition::At { proposition, .. } => {
                matches!(proposition.as_ref(), ClickProposition::Separate { .. })
            }
            _ => false,
        };
        if selected_surface_separation
            && !body_facts.contains(&body_kernel)
            && body_facts.assumptions().proves(&body_kernel)
        {
            body_facts = body_facts.with_fact(body_kernel.clone());
        }
        for name in self.focused_goal_unfolds().iter() {
            let recorded_bodies = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Point(context) => context
                    .surface_propositions
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => self
                    .outcome_point_view()
                    .into_iter()
                    .flat_map(|view| view.surface_propositions.kernels_written_by_predicate(name))
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            for recorded in recorded_bodies {
                if matches!(recorded, Proposition::ForAll { .. })
                    && body_facts.contains_top_level(&recorded)
                {
                    body_facts = body_facts.with_predicate_unfold_fact(recorded);
                }
            }
        }
        let body_context = GoalContext {
            facts: body_facts,
            unfolded_predicates: self.focused_goal_unfolds().clone(),
            execution: self.goal_execution().cloned(),
        };
        // An execution `have` borrows the current immutable frontier solely
        // as its proposition-lowering/theorem context, shared by identity on
        // the nested goal; a `have` stated at a function outcome borrows that
        // outcome's result-aware point data the same way. The nested goal
        // cannot publish a changed frontier or outcome: `join` restores the
        // exact root state and exposes only the stated proposition.
        let mut body_goal = match self.focused_outcome_point() {
            Some(point) => Goal::surface_proposition_at_outcome(
                body_context,
                point.clone(),
                body_kernel.clone(),
                structural_proposition,
            ),
            None => Goal::surface_proposition_in(body_context, body_kernel, structural_proposition),
        };
        if let (Some(Goal::Proposition(parent)), Goal::Proposition(body)) =
            (self.focused_goal(), &mut body_goal)
        {
            body.surface_bindings = parent.surface_bindings.clone();
        }
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals: ProofGoals::root(body_goal),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: GoalId::ROOT,
                depth: 0,
            }),
            focused: GoalId::ROOT,
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Have {
                proposition,
                kernel,
            }),
            body,
            introduced_facts: Vec::new(),
        })
    }

    /// Opens one composite resource body as an execution scope. Entry is an
    /// audited representation transition, not a separately serialized
    /// `unfold`; the child Proof starts fresh provenance and the eventual join
    /// records the child certificate inside one `Open` step.
    pub(super) fn begin_open(
        &self,
        resource: ResourceClause,
        source_index: usize,
    ) -> Result<ProofScope<'a>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`open` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`open`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(self.step_error("`open` must begin before execution reaches function exit"));
        }
        let checked = open_composite_resource_for_proof(
            context.resource_environment,
            &resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.state).clone(),
            self.facts().clone(),
            &mut execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.state = checked.state.into();
        execution.replay.open_scopes += 1;
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let introduced_facts = checked.added_facts.clone();
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals: self
                    .state
                    .goals
                    .replace_frontier_at(self.focused, checked.facts, execution),
                added_facts: Arc::new(checked.added_facts.clone()),
                checked_facts: Arc::new(checked.added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused: self.focused,
                depth: 0,
            }),
            focused: self.focused,
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Open {
                resource,
                source_index,
                preserve_exposed_body: checked.body_was_already_exposed,
            }),
            body,
            introduced_facts,
        })
    }

    /// Opens the C `if` at an execution frontier into its kernel-feasible
    /// checked arms.
    ///
    /// This is a structural operation rather than a surface `Step`: branch
    /// entry owns condition certification, path-fact admission, and movement
    /// to each selected arm. The enclosing `Branch` certificate is recorded
    /// only when those descendants join.
    /// Performs the audited C-branch entry work shared by the container
    /// and the in-`Proof` sibling split: guards, source resolution, the
    /// kernel condition transitions, and each feasible arm's checked facts,
    /// snapshot, path-fact delta, and condition theorem. There is exactly
    /// one implementation of this branch-entry law.
    fn prepare_execution_branch(&self) -> Result<PreparedExecutionBranch, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`branch` requires an execution-frontier proof"));
        };
        if self.state.goals.is_discharged()
            || !matches!(self.focused_goal(), Some(Goal::Frontier(_)))
        {
            return Err(self.step_error("`branch` requires an open execution frontier"));
        }
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let statement_index = execution.replay.frontier.next_statement_index;
        let source_region = execution
            .replay
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                self.step_error(format!(
                    "`branch` could not resolve source statement({statement_index})"
                ))
            })?;
        let SourceStatementKind::If {
            then_statement_index,
            else_statement_index,
        } = source_region.kind
        else {
            return Err(self.step_error(format!(
                "`branch` requires a C `if` at the execution frontier, but statement({statement_index}) is not an `if`"
            )));
        };
        let initial_continuation_depth = execution.replay.frontier.continuations.len();
        let (execution_start_state, current_state, statement, remaining) =
            next_top_level_statement_from_execution_point(
                &execution.replay,
                &execution.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(self.step_error("`branch` source region did not contain a C `if`"));
        };
        let surface_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let transitions = certified_proof_condition_transitions(
            &current_state,
            &self.facts(),
            &condition,
            &format!(
                "`{}` tactic {}: `branch`",
                context.claim_label, context.tactic_index
            ),
        )?;
        let mut arms: [Option<PreparedExecutionArm>; 2] = [None, None];
        for transition in transitions {
            let take_then = transition.is_true;
            let selected_branch = if take_then {
                then_branch.as_ref()
            } else {
                else_branch.as_ref()
            };
            let mut arm_execution = execution.clone();
            arm_execution.replay.completed_branch_regions.clear();
            record_statement_program_point_state(
                &mut arm_execution.replay,
                context.function_block,
                statement_index,
                ProgramPointKind::Entry,
                current_state.clone(),
            );
            let resolved_state = crate::kernel::resolve_pending_heap_allocations(
                &current_state,
                transition.pure_facts.assumptions(),
            );
            if resolved_state.memory().has_pending_heap_allocation() {
                return Err(self.step_error(
                    "checked `branch` cannot yet own an unresolved heap-allocation outcome split",
                ));
            }
            arm_execution
                .replay
                .frontier
                .continuations
                .push(ProofExecutionContinuation {
                    remaining: remaining.clone().map(Arc::new),
                    next_statement_index: source_region.continuation_node,
                    kind: ProofExecutionContinuationKind::Branch { statement_index },
                });
            arm_execution.replay.frontier.next_statement_index = if take_then {
                then_statement_index
            } else {
                else_statement_index
            };
            arm_execution.replay.frontier.execution_start_state =
                Some(execution_start_state.clone());
            arm_execution.state = resolved_state.into();
            if matches!(selected_branch, CStatement::Skip) {
                let Some(remaining) = resume_after_completed_region(
                    &mut arm_execution.replay,
                    context.function_block,
                    &arm_execution.state,
                ) else {
                    return Err(self.step_error("`branch` reached function end without a return"));
                };
                arm_execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
                    remaining: remaining.into(),
                };
            } else {
                arm_execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
                    remaining: Arc::new(selected_branch.clone()),
                };
            }
            record_current_statement_entry(
                &mut arm_execution.replay,
                &arm_execution.state,
                context.function_block,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "branch",
            )?;
            let surface_path_fact = if take_then {
                surface_condition.clone()
            } else {
                negate_click_proposition(&surface_condition)
            };
            let pre_state = arm_execution
                .replay
                .old_reference_state(&arm_execution.state);
            let kernel_path_fact = lower_point_proposition_with_assumptions(
                &surface_path_fact,
                transition.pure_facts.assumptions(),
                context.parsed_function.parameters(),
                context.arguments,
                pre_state,
                &arm_execution.state,
                None,
                &arm_execution.replay.program_point_states,
                context.predicate_environment,
                context.click_function_environment,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "could not retain the checked C branch condition form: {message}"
                ))
            })?;
            arm_execution
                .replay
                .surface_propositions
                .record_lowering(&surface_path_fact, &kernel_path_fact)?;
            arm_execution
                .branch_surface_facts
                .insert(kernel_path_fact.clone());
            arm_execution
                .branch_decisions
                .push(ExecutionBranchDecision {
                    condition: surface_condition.clone(),
                    value: take_then,
                });
            arm_execution.replay.has_structured_branch_history = true;
            arm_execution.branch_path.push(format!(
                "{} arm of C `if` at statement({statement_index})",
                if take_then { "then" } else { "else" }
            ));
            let mut introduced_facts = PersistentOrderedSet::default();
            for fact in &transition.path_facts {
                introduced_facts.insert(fact.clone());
            }
            arms[usize::from(!take_then)] = Some(PreparedExecutionArm {
                facts: transition.pure_facts,
                execution: arm_execution,
                path_facts: transition.path_facts,
                introduced_facts,
                condition_theorem: transition.theorem,
            });
        }
        if arms.iter().all(Option::is_none) {
            return Err(self.step_error("`branch` found no feasible C `if` arm"));
        }
        Ok(PreparedExecutionBranch {
            statement_index,
            continuation_index: source_region.continuation_node,
            continuation_remaining: remaining.map(Arc::new),
            execution_start_state,
            initial_continuation_depth,
            arms,
        })
    }

    /// Splits the focused execution frontier at a C `if` into sibling
    /// frontier goals inside this same proof state: the in-`Proof` form of
    /// the execution branch. Each kernel-feasible arm becomes one sibling
    /// goal owning its checked arm facts and snapshot; the returned record
    /// carries the split identity, per-arm condition theorems, split-time
    /// fact bases for `introduced_since`, and the shared continuation data
    /// its joins verify — bookkeeping, never semantic authority.
    /// The delta checks both execution join variants share: the arm kept
    /// its recorded condition polarity, and every replay store the join
    /// migrates changed by exactly the arm's claimed introduction delta,
    /// while the unmigrated stores did not change at all.
    fn validate_execution_join_arm_deltas(
        &self,
        variant: &str,
        name: &str,
        expected: bool,
        arm: &CheckedExecutionJoinArm<'_>,
        parent_execution: &ExecutionProofState,
    ) -> Result<(), ClickError> {
        if let Some(condition_theorem) = arm.condition_theorem
            && !matches!(
                implication_body(condition_theorem.proposition()),
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::Value(actual),
                    ..
                } if *actual == expected
            )
        {
            return Err(self.step_error(format!("{name} arm retained the wrong condition theorem")));
        }
        let replay = &arm.execution.replay;
        if replay.function_entry_execution_prerequisites.len()
            != parent_execution
                .replay
                .function_entry_execution_prerequisites
                .len()
                + arm.introduced_prerequisites.len()
            || replay.function_entry_derivations.len()
                != parent_execution.replay.function_entry_derivations.len()
                    + arm.introduced_derivations.len()
            || replay.frontier_loop_clauses.len()
                != parent_execution.replay.frontier_loop_clauses.len()
            || replay.frontier_loop_rules.len() != parent_execution.replay.frontier_loop_rules.len()
            || replay.unfolded_predicates.len()
                != parent_execution.replay.unfolded_predicates.len() + arm.introduced_unfolds.len()
            || replay.planned_statement_transitions.len()
                != parent_execution.replay.planned_statement_transitions.len()
        {
            return Err(self.step_error(format!(
                "{name} execution arm changed replay metadata that the checked {variant} has not migrated"
            )));
        }
        Ok(())
    }

    /// The retention law for a decided `branch ensuring`: the explicit
    /// interface is validated on the sole kernel-feasible arm with no
    /// abstraction or resource merge — the surviving checked state remains
    /// the successor, so ownership assertions are safe here even though
    /// two-arm ownership normalization has not migrated. Produces the arm's
    /// post-interface context and the structured `Branch { ensuring, .. }`
    /// with an empty impossible arm.
    #[allow(clippy::too_many_arguments)]
    fn merge_decided_interface_execution_path(
        &self,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        continuation_index: usize,
        initial_continuation_depth: usize,
        take_then: bool,
        assertions: Vec<ProofAssertion>,
        arm: &CheckedExecutionJoinArm<'_>,
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        let replay = &arm.execution.replay;
        let reached_continuation = replay.completed_branch_regions.contains(&statement_index)
            && replay.frontier.continuations.len() <= initial_continuation_depth
            && replay.frontier.next_statement_index == continuation_index;
        let reached_exit = replay.is_at_function_exit()
            && replay.frontier.continuations.len() <= initial_continuation_depth;
        if !reached_continuation && !reached_exit {
            return Err(self.step_error(format!(
                "the sole feasible {} `branch ensuring` arm has not reached its continuation or function exit",
                if take_then { "then" } else { "else" }
            )));
        }
        self.validate_execution_join_arm_deltas(
            "path operation",
            "the decided interface",
            take_then,
            arm,
            parent_execution,
        )?;

        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(continuation_index),
            kind: ProgramPointKind::Entry,
        };
        let mut execution = arm.execution.clone();
        let mut state = (*execution.state).clone();
        let mut facts = arm.facts.clone();
        let facts_before_interface = facts.clone();
        apply_branch_interface_with_proof_facts(
            &target,
            &assertions,
            context.tactic_index,
            &mut execution.replay,
            &mut state,
            &mut facts,
            context.parsed_function.parameters(),
            context.arguments,
            context.predicate_environment,
            context.click_function_environment,
            context.resource_environment,
            context.claim_label,
            &BTreeMap::new(),
            None,
            false,
        )
        .map_err(|error| add_proof_branch_path(error, &execution.branch_path))?;
        execution.state = state.into();
        execution.branch_path = parent_execution.branch_path.clone();
        execution.replay.case_assumptions = parent_execution.replay.case_assumptions.clone();

        let mut added_facts = arm.introduced_facts.clone();
        for assertion in &assertions {
            let ProofAssertion::Fact(surface) = assertion else {
                continue;
            };
            if let Some(fact) = execution.replay.surface_propositions.unique_kernel(surface)
                && !facts_before_interface.contains_top_level(fact)
                && !added_facts.contains(fact)
            {
                added_facts.push(fact.clone());
            }
        }
        let selected = arm.certificate.clone();
        let empty = ProofCertificate::from_steps(Vec::new());
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };
        let unfolded_predicates =
            arm.introduced_unfolds
                .iter()
                .fold(parent_unfolds.clone(), |mut unfolds, name| {
                    unfolds.insert(name.clone());
                    unfolds
                });
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts: added_facts,
            unfolded_predicates,
            step: SimpleProofStep::Branch {
                ensuring: Some(assertions),
                then_proof: Box::new(then_proof),
                else_proof: Box::new(else_proof),
            },
        })
    }

    /// The retention law for a decided execution branch: the kernel
    /// certified exactly one feasible arm, so the surviving descendant's
    /// context becomes the successor while a logical `If` records the
    /// checked source condition and an empty contradictory arm. Verifies
    /// arrival at the shared continuation or function exit, condition
    /// polarity, and the migrated replay deltas, and produces the `If`
    /// step. Callers assemble the successor around the arm's own context.
    fn merge_decided_execution_path(
        &self,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        continuation_index: usize,
        initial_continuation_depth: usize,
        take_then: bool,
        arm: &CheckedExecutionJoinArm<'_>,
    ) -> Result<SimpleProofStep, ClickError> {
        let replay = &arm.execution.replay;
        let reached_continuation = replay.completed_branch_regions.contains(&statement_index)
            && replay.frontier.continuations.len() <= initial_continuation_depth
            && replay.frontier.next_statement_index == continuation_index;
        let reached_exit = replay.is_at_function_exit()
            && replay.frontier.continuations.len() <= initial_continuation_depth;
        if !reached_continuation && !reached_exit {
            return Err(self.step_error(format!(
                "the sole feasible {} execution arm has not reached its continuation or function exit",
                if take_then { "then" } else { "else" }
            )));
        }
        self.validate_execution_join_arm_deltas(
            "path operation",
            "the decided",
            take_then,
            arm,
            parent_execution,
        )?;

        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &parent_execution.replay,
            &parent_execution.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "decided branch",
        )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(
                self.step_error("decided execution branch root no longer points at a C `if`")
            );
        };
        let surface_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let source_arm = if take_then {
            then_branch.as_ref()
        } else {
            else_branch.as_ref()
        };
        let entry_steps = 1 + usize::from(matches!(source_arm, CStatement::Skip));
        let path_condition = if take_then {
            surface_condition.clone()
        } else {
            negate_click_proposition(&surface_condition)
        };
        let mut selected_steps = Vec::with_capacity(entry_steps + arm.certificate.steps().len());
        selected_steps.push(SimpleProofStep::StepUsing(vec![path_condition]));
        selected_steps.resize_with(entry_steps, || SimpleProofStep::StepUsing(Vec::new()));
        selected_steps.extend_from_slice(arm.certificate.steps());
        let selected = ProofCertificate::from_steps(selected_steps);
        let empty = ProofCertificate::from_steps(Vec::new());
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };
        Ok(SimpleProofStep::If {
            condition: surface_condition,
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        })
    }

    fn common_resources_after_interface_consumption(
        &self,
        parent_execution: &ExecutionProofState,
        arms: &[CheckedExecutionJoinArm<'_>; 2],
        assertions: &[ProofAssertion],
    ) -> Result<ResourceContext, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource interface requires an execution proof"));
        };
        let mut then_residual = arms[0].execution.state.resources().clone();
        let mut else_residual = arms[1].execution.state.resources().clone();
        for assertion in assertions {
            let ProofAssertion::Resource(resource) = assertion else {
                continue;
            };
            let then_expected = lower_resource_clause_at_state(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &arms[0].execution.state,
            )?;
            if !then_expected.is_own() {
                continue;
            }
            let else_expected = lower_resource_clause_at_state(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &arms[1].execution.state,
            )?;
            then_residual = then_residual
                .without_fact_incrementally(&then_expected, arms[0].facts.assumptions())
                .ok_or_else(|| {
                    self.step_error(
                        "then arm could not consume its established `branch ensuring` ownership representation",
                    )
                })?;
            else_residual = else_residual
                .without_fact_incrementally(&else_expected, arms[1].facts.assumptions())
                .ok_or_else(|| {
                    self.step_error(
                        "else arm could not consume its established `branch ensuring` ownership representation",
                    )
                })?;
        }
        ResourceContext::common_exact_descendant(
            &then_residual,
            &else_residual,
            parent_execution.state.resources(),
        )
        .ok_or_else(|| {
            self.step_error(
                "checked `branch ensuring` resource snapshots do not descend from the branch root",
            )
        })
    }

    /// The merge law for a checked two-arm interface join: each arm is
    /// independently abstracted through the explicit `branch ensuring`
    /// interface before any result is selected, the join is accepted only
    /// when the abstract states and exported facts agree exactly, and the
    /// owned resource interface is consumed from both concrete arms before
    /// intersecting their residuals. Produces the abstract continuation
    /// context and the `Branch { ensuring, .. }` step.
    #[allow(clippy::too_many_arguments)]
    fn merge_interface_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        continuation_index: usize,
        continuation_remaining: &Option<Arc<CStatement>>,
        execution_start_state: CState,
        assertions: Vec<ProofAssertion>,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        let join_continuation = derive_execution_join_continuation(
            parent_execution,
            continuation_remaining,
            continuation_index,
        )
        .ok_or_else(|| {
            self.step_error("execution `branch` has no shared continuation statement")
        })?;
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            let replay = &arm.execution.replay;
            if !replay.completed_branch_regions.contains(&statement_index)
                || join_continuation
                    .completed_enclosing_branches
                    .iter()
                    .any(|statement_index| {
                        !replay.completed_branch_regions.contains(statement_index)
                    })
                || !replay
                    .frontier
                    .continuations
                    .shares_tail_with(&join_continuation.continuations)
                || replay.frontier.next_statement_index != join_continuation.next_statement_index
                || !matches!(
                    &replay.frontier.point,
                    ProofExecutionPoint::StatementEntry { remaining }
                        if remaining.as_ref() == join_continuation.remaining.as_ref()
                )
                || replay.is_at_function_exit()
            {
                return Err(self.step_error(format!(
                    "{name} `branch ensuring` arm has not reached its shared continuation"
                )));
            }
            self.validate_execution_join_arm_deltas(
                "interface join",
                name,
                expected,
                arm,
                parent_execution,
            )?;
        }
        let common_program_points = arms[0]
            .execution
            .replay
            .program_point_states
            .common_descendant(
                &arms[1].execution.replay.program_point_states,
                &parent_execution.replay.program_point_states,
            )
            .ok_or_else(|| {
                self.step_error(
                    "`branch ensuring` arms do not descend from the root program-point state",
                )
            })?;

        let mut stable_join_locals = arms[0]
            .execution
            .state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        stable_join_locals
            .retain(|name, value| arms[1].execution.state.locals().get(name) == Some(value));
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(join_continuation.next_statement_index),
            kind: ProgramPointKind::Entry,
        };
        let sibling_join_states: [&CState; 2] =
            [&arms[0].execution.state, &arms[1].execution.state];

        let abstract_arm = |arm: &CheckedExecutionJoinArm<'_>| -> Result<
            (ExecutionProofState, ProofFacts),
            ClickError,
        > {
            let mut execution = arm.execution.clone();
            let mut facts = arm.facts.clone();
            let mut state = (*execution.state).clone();
            let ProofContext::Execution(context) = self.context.as_ref() else {
                unreachable!("execution branch retained a non-execution context")
            };
            apply_branch_interface_with_proof_facts(
                &target,
                &assertions,
                context.tactic_index,
                &mut execution.replay,
                &mut state,
                &mut facts,
                context.parsed_function.parameters(),
                context.arguments,
                context.predicate_environment,
                context.click_function_environment,
                context.resource_environment,
                context.claim_label,
                &stable_join_locals,
                Some(&sibling_join_states),
                true,
            )
            .map_err(|error| add_proof_branch_path(error, &execution.branch_path))?;
            execution.state = state.into();
            Ok((execution, facts))
        };
        let (mut then_abstract, then_interface_facts) = abstract_arm(&arms[0])?;
        let (else_abstract, else_interface_facts) = abstract_arm(&arms[1])?;

        let then_interface_vec = then_interface_facts.to_vec();
        let else_interface_vec = else_interface_facts.to_vec();
        if then_interface_vec != else_interface_vec || *then_abstract.state != *else_abstract.state
        {
            return Err(self.step_error(
                "`branch ensuring` arms produced different abstract successor states",
            ));
        }

        // Consume owned exports from both concrete arms before intersecting
        // their exact residuals. Re-adding the normalized interface below
        // therefore neither duplicates a common representation nor loses the
        // portion of ownership selected by the interface.
        let common_resources = self.common_resources_after_interface_consumption(
            parent_execution,
            &arms,
            &assertions,
        )?;

        // Owned interface facts were consumed above and must be restored once.
        // Duplicable views are added only when the residual common context
        // does not already establish them.
        let mut resources = common_resources;
        let additions = then_abstract
            .state
            .resources()
            .facts()
            .iter()
            .filter(|fact| {
                fact.is_own() || !resources.satisfies_fact(fact, then_interface_facts.assumptions())
            })
            .cloned()
            .collect::<Vec<_>>();
        resources = resources
            .try_compose_into_valid_context_delaying_normalization(
                additions.iter().cloned(),
                then_interface_facts.assumptions(),
            )
            .map_err(|error| {
                self.step_error(format!(
                    "invalid automatic common `branch ensuring` resource interface: {error:?}"
                ))
            })?
            .normalized_around_facts(&additions, then_interface_facts.assumptions());
        let state = (*then_abstract.state)
            .clone()
            .with_resource_context(resources);
        then_abstract.state = state.into();

        let abstract_state = (*then_abstract.state).clone();
        let mut execution = parent_execution.clone();
        execution.has_empty_execution_branch_leaf |= then_abstract.has_empty_execution_branch_leaf
            || else_abstract.has_empty_execution_branch_leaf;
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [&then_abstract, &else_abstract],
        )?;
        execution.state = abstract_state.clone().into();
        execution.replay.program_point_states = common_program_points;
        execution
            .replay
            .program_point_states
            .insert(target, abstract_state.clone());
        execution.replay.completed_branch_regions.clear();
        execution
            .replay
            .completed_branch_regions
            .insert(statement_index);
        for statement_index in &join_continuation.completed_enclosing_branches {
            execution
                .replay
                .completed_branch_regions
                .insert(*statement_index);
        }
        execution.replay.frontier.next_statement_index = join_continuation.next_statement_index;
        execution.replay.frontier.continuations = join_continuation.continuations;
        execution.replay.frontier.execution_start_state = Some(execution_start_state);
        execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: join_continuation.remaining,
        };
        execution.replay.has_structured_branch_history = true;
        execution.replay.execution_abstraction = true;
        execution.replay.unfolded_predicates.clear();
        execution.replay.case_assumptions.clear();
        execution.replay.next_opaque_call = then_abstract
            .replay
            .next_opaque_call
            .max(else_abstract.replay.next_opaque_call);
        execution.replay.next_kernel_variable = then_abstract
            .replay
            .next_kernel_variable
            .max(else_abstract.replay.next_kernel_variable);
        for effect in arms[0]
            .introduced_effect_facts
            .iter()
            .chain(&arms[1].introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in arms[0]
            .introduced_prerequisites
            .iter()
            .chain(&arms[1].introduced_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in arms[0]
            .introduced_derivations
            .iter()
            .chain(&arms[1].introduced_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path.clear();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_point_state(
            &mut execution.replay,
            context.function_block,
            statement_index,
            ProgramPointKind::Exit,
            abstract_state,
        );
        record_current_statement_entry(
            &mut execution.replay,
            &execution.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "branch ensuring",
        )?;

        let mut facts = parent_facts.clone();
        let mut added_facts = Vec::new();
        let mut retain_fact = |fact: &Proposition| -> Result<(), ClickError> {
            if !facts.contains_top_level(fact) {
                facts = facts.with_fact(fact.clone());
                added_facts.push(fact.clone());
            }
            for surface in then_abstract.replay.surface_propositions.surfaces(fact) {
                if else_abstract
                    .replay
                    .surface_propositions
                    .surfaces(fact)
                    .any(|candidate| candidate == surface)
                {
                    execution
                        .replay
                        .surface_propositions
                        .record_lowering(surface, fact)?;
                }
            }
            Ok(())
        };
        for fact in &then_interface_vec {
            retain_fact(fact)?;
        }
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        for fact in &arms[0].introduced_facts {
            if else_introduced.contains(fact)
                && arms[0].facts.contains(fact)
                && arms[1].facts.contains(fact)
            {
                retain_fact(fact)?;
            }
        }

        #[cfg(test)]
        CHECKED_EXECUTION_INTERFACE_JOINS.with(|count| count.set(count.get() + 1));

        let [then_view, else_view] = arms;
        let step = SimpleProofStep::Branch {
            ensuring: Some(assertions),
            then_proof: Box::new(then_view.certificate),
            else_proof: Box::new(else_view.certificate),
        };
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts: added_facts,
            unfolded_predicates: parent_unfolds.clone(),
            step,
        })
    }

    /// Joins the two sibling execution frontier goals created by
    /// [`Proof::split_focused_execution_branch`] through one explicit
    /// common frontier interface, resuming the parent obligation under its
    /// original id with the abstract continuation context. A one-arm split
    /// is a decided path: the interface is validated on the sole sibling
    /// with no abstraction or resource merge, as in the container form.
    pub(super) fn join_focused_execution_interface(
        &self,
        record: &ExecutionSplit<'a>,
        assertions: Vec<ProofAssertion>,
    ) -> Result<Self, ClickError> {
        let sole_arm = match record.ids {
            [Some(id), None] => Some((true, 0usize, id)),
            [None, Some(id)] => Some((false, 1, id)),
            _ => None,
        };
        if let Some((take_then, arm_index, id)) = sole_arm {
            let [mut steps, trailing] =
                self.partition_steps_since(&record.marker, record.split, [id, id])?;
            steps.extend(trailing);
            let name = if take_then { "then" } else { "else" };
            let (selection, view) =
                self.sibling_execution_arm_view(record, name, arm_index, id, steps)?;
            let parts = self.merge_decided_interface_execution_path(
                &record.parent_unfolds,
                &record.parent_execution,
                record.statement_index,
                record.continuation_index,
                record.initial_continuation_depth,
                take_then,
                assertions,
                &view,
            )?;
            return self.resume_parent_after_sibling_join(record, [id, id], selection, parts);
        }
        let (ids, selection, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_interface_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            &record.continuation_remaining,
            record.execution_start_state.clone(),
            assertions,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, selection, parts)
    }

    /// Carries only checked C-branch anchor spellings across a structural
    /// join. The persistent fact set is owned by `Proof`; it retains exact
    /// historical premises and extraction spellings without publishing
    /// unrelated arm-local predicate or resource provenance.
    fn merge_branch_surface_facts(
        &self,
        execution: &mut ExecutionProofState,
        parent: &ExecutionProofState,
        arms: [&ExecutionProofState; 2],
    ) -> Result<(), ClickError> {
        for arm in arms {
            let introduced = arm
                .branch_surface_facts
                .introduced_since(&parent.branch_surface_facts)
                .ok_or_else(|| {
                    self.step_error(
                        "execution branch surface facts do not descend from the split root",
                    )
                })?;
            for fact in introduced {
                for surface in arm.replay.surface_propositions.surfaces(&fact) {
                    execution
                        .replay
                        .surface_propositions
                        .record_lowering(surface, &fact)?;
                }
                execution.branch_surface_facts.insert(fact);
            }
        }
        Ok(())
    }

    /// The merge law for a terminal two-arm execution join: both arms
    /// completed at function exit, so distinct return outcomes remain as
    /// separate paths instead of requiring one equal C state. Produces the
    /// function-exit continuation context and the structured logical `If`
    /// step, wrapping each arm's body certificate with its explicit entry
    /// steps. Callers assemble the successor proof.
    #[allow(clippy::too_many_arguments)]
    fn merge_terminal_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        execution_start_state: CState,
        initial_continuation_depth: usize,
        proof_case_condition: Option<ClickProposition>,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        if !arms[0]
            .execution
            .state
            .resources()
            .shares_storage_with(arms[1].execution.state.resources())
        {
            return Err(self.step_error(
                "checked `branch ensuring` cannot yet retain a proper common resource delta",
            ));
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("terminal execution join retained a non-execution context")
        };
        let proof_case_split = proof_case_condition.is_some();
        let (surface_condition, empty_source_arms) = if let Some(condition) = proof_case_condition {
            (condition, [false, false])
        } else {
            let (_, _, statement, _) = next_top_level_statement_from_execution_point(
                &parent_execution.replay,
                &parent_execution.state,
                context.function,
                context.arguments,
                context.claim_label,
                context.tactic_index,
                "terminal branch join",
            )?;
            let CStatement::If {
                condition,
                then_branch,
                else_branch,
            } = statement
            else {
                return Err(
                    self.step_error("terminal execution branch root no longer points at a C `if`")
                );
            };
            (
                surface_with_source_site(
                    &surface_c_condition(&condition),
                    &ProgramPointRef {
                        region: CodeRegionRef::Statement(statement_index),
                        kind: ProgramPointKind::Entry,
                    },
                )?,
                [
                    matches!(then_branch.as_ref(), CStatement::Skip),
                    matches!(else_branch.as_ref(), CStatement::Skip),
                ],
            )
        };
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            let replay = &arm.execution.replay;
            if !replay.is_at_function_exit()
                || replay.frontier.continuations.len() > initial_continuation_depth
            {
                return Err(self.step_error(format!(
                    "{name} branch arm has not completed at function exit (at exit: {}, continuation depth: {}, root depth: {})",
                    replay.is_at_function_exit(),
                    replay.frontier.continuations.len(),
                    initial_continuation_depth,
                )));
            }
            self.validate_execution_join_arm_deltas(
                "terminal join",
                name,
                expected,
                arm,
                parent_execution,
            )?;
        }

        let terminal_certificate =
            |body: &ProofCertificate, empty_source_arm: bool, path_condition: ClickProposition| {
                let entry_steps = 1 + usize::from(empty_source_arm);
                let mut steps = Vec::with_capacity(entry_steps + body.steps().len());
                steps.push(SimpleProofStep::StepUsing(vec![path_condition]));
                steps.resize_with(entry_steps, || SimpleProofStep::StepUsing(Vec::new()));
                steps.extend_from_slice(body.steps());
                ProofCertificate::from_steps(steps)
            };
        let then_proof = if proof_case_split {
            arms[0].certificate.clone()
        } else {
            terminal_certificate(
                &arms[0].certificate,
                empty_source_arms[0],
                surface_condition.clone(),
            )
        };
        let else_proof = if proof_case_split {
            arms[1].certificate.clone()
        } else {
            terminal_certificate(
                &arms[1].certificate,
                empty_source_arms[1],
                negate_click_proposition(&surface_condition),
            )
        };
        let then_replay = &arms[0].execution.replay;
        let else_replay = &arms[1].execution.replay;
        let common_program_points = then_replay
            .program_point_states
            .common_descendant(
                &else_replay.program_point_states,
                &parent_execution.replay.program_point_states,
            )
            .ok_or_else(|| {
                self.step_error(
                    "terminal execution arms do not descend from the branch root's program points",
                )
            })?;

        // Root facts remain shared in `ProofState`. Only facts introduced in
        // one arm need to be copied into that arm's returned execution paths;
        // doing so avoids duplicating the complete ambient proof context per
        // outcome.
        let mut paths = Vec::new();
        let mut path_branch_decisions: Vec<PersistentSequence<ExecutionBranchDecision>> =
            Vec::new();
        for (arm_index, arm) in arms.iter().enumerate() {
            let completed = arm
                .execution
                .replay
                .execution()
                .expect("validated terminal arm is at function exit");
            for (arm_path_index, path) in completed.paths().iter().enumerate() {
                let mut path_facts = path.execution_facts();
                for proposition in &arm.introduced_facts {
                    let fact = ExecutionPureFact::new(proposition.clone());
                    if !path_facts.contains(&fact) {
                        path_facts.push(fact);
                    }
                }
                let obligations = path.obligations().to_vec();
                if !paths
                    .iter()
                    .any(|(existing_outcome, existing_facts, existing_obligations)| {
                        existing_outcome == path.outcome()
                            && existing_facts == &path_facts
                            && existing_obligations == &obligations
                    })
                {
                    paths.push((path.outcome().clone(), path_facts, obligations));
                    let mut decisions = arm
                        .execution
                        .outcome_branch_decisions
                        .get(arm_path_index)
                        .cloned()
                        .unwrap_or_else(|| arm.execution.branch_decisions.clone());
                    if proof_case_split {
                        decisions.push(ExecutionBranchDecision {
                            condition: surface_condition.clone(),
                            value: arm_index == 0,
                        });
                    }
                    path_branch_decisions.push(decisions);
                }
            }
        }

        let outcomes = c_function_execution_candidates_from_outcomes(
            execution_start_state.clone(),
            context.function.clone(),
            context.arguments.to_vec(),
            paths,
        );
        let mut execution = parent_execution.clone();
        execution.has_empty_execution_branch_leaf |= arms
            .iter()
            .any(|arm| arm.execution.has_empty_execution_branch_leaf);
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
        )?;
        execution.state = execution_start_state.clone().into();
        execution.replay.program_point_states = common_program_points;
        if !proof_case_split {
            execution
                .replay
                .completed_branch_regions
                .insert(statement_index);
        }
        for continuation in &parent_execution.replay.frontier.continuations {
            if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
                execution
                    .replay
                    .completed_branch_regions
                    .insert(statement_index);
            }
        }
        execution.replay.frontier.continuations.clear();
        execution.replay.frontier.execution_start_state = Some(execution_start_state);
        execution.replay.frontier.point = ProofExecutionPoint::FunctionExit {
            execution: outcomes,
        };
        execution.branch_decisions = parent_execution.branch_decisions.clone();
        execution.outcome_branch_decisions = Arc::new(path_branch_decisions);
        execution.replay.has_structured_branch_history = true;
        execution.replay.next_opaque_call = then_replay
            .next_opaque_call
            .max(else_replay.next_opaque_call);
        execution.replay.next_kernel_variable = then_replay
            .next_kernel_variable
            .max(else_replay.next_kernel_variable);
        for effect in arms[0]
            .introduced_effect_facts
            .iter()
            .chain(&arms[1].introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in arms[0]
            .introduced_prerequisites
            .iter()
            .chain(&arms[1].introduced_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in arms[0]
            .introduced_derivations
            .iter()
            .chain(&arms[1].introduced_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            if !execution.replay.unfolded_predicates.contains(name) {
                execution.replay.unfolded_predicates.push(name.clone());
            }
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path = parent_execution.branch_path.clone();
        execution.replay.case_assumptions = parent_execution.replay.case_assumptions.clone();

        // A selected-site capture is attribution metadata for one source
        // occurrence. It may be inherited unchanged by both arms, or begin
        // in exactly one arm. Retain that cursor across the audited join, but
        // reject two different captures rather than guessing which source
        // occurrence owns the eventual expansion.
        let parent_capture = parent_execution.replay.deferred_tactic_capture.as_ref();
        let then_capture = then_replay.deferred_tactic_capture.as_ref();
        let else_capture = else_replay.deferred_tactic_capture.as_ref();
        if parent_capture.is_some()
            && (then_capture != parent_capture || else_capture != parent_capture)
        {
            return Err(
                self.step_error("terminal execution arm lost its inherited selected-tactic cursor")
            );
        }
        execution.replay.deferred_tactic_capture = match (then_capture, else_capture) {
            (Some(then_capture), Some(else_capture)) if then_capture == else_capture => {
                Some(then_capture.clone())
            }
            (Some(capture), None) if parent_capture.is_none() => {
                let mut capture = capture.clone();
                capture.branch_skeleton = vec![ProofTactic::If(ProofIf {
                    condition: surface_condition.clone(),
                    then_tactics: capture.branch_skeleton,
                    else_tactics: Vec::new(),
                })];
                Some(capture)
            }
            (None, Some(capture)) if parent_capture.is_none() => {
                let mut capture = capture.clone();
                capture.branch_skeleton = vec![ProofTactic::If(ProofIf {
                    condition: surface_condition.clone(),
                    then_tactics: Vec::new(),
                    else_tactics: capture.branch_skeleton,
                })];
                Some(capture)
            }
            (None, None) => None,
            _ => {
                return Err(self.step_error(
                    "terminal execution arms retained different selected-tactic cursors",
                ));
            }
        };

        // Terminal arm tactics are source-order cursors, not semantic state.
        // Preserve only the append-only suffix each checked arm added after
        // the split root, nested under the exact condition this audited join
        // retained in its `If` provenance. Ordered finalization later asks
        // each focused outcome Proof to select one arm and apply those
        // ordinary operations; the joined execution frontier gains no facts,
        // C state, resources, or successor authority from this tree.
        let then_post_execution = then_replay
            .post_execution_tactics
            .suffix_since(&parent_execution.replay.post_execution_tactics)
            .ok_or_else(|| {
                self.step_error(
                    "terminal then-arm finalization cursor does not descend from the split root",
                )
            })?;
        let else_post_execution = else_replay
            .post_execution_tactics
            .suffix_since(&parent_execution.replay.post_execution_tactics)
            .ok_or_else(|| {
                self.step_error(
                    "terminal else-arm finalization cursor does not descend from the split root",
                )
            })?;
        if !then_post_execution.is_empty() || !else_post_execution.is_empty() {
            let attribution = then_post_execution
                .first()
                .or_else(|| else_post_execution.first())
                .expect("a nonempty terminal cursor has one attributed operation");
            execution.replay.defer_post_execution(
                attribution.tactic_index,
                attribution.source_index,
                PostExecutionTactic::If {
                    condition: surface_condition.clone(),
                    then_tactics: then_post_execution,
                    else_tactics: else_post_execution,
                },
            );
        }

        let mut facts = parent_facts.clone();
        let mut common_added_facts = Vec::new();
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        for fact in &arms[0].introduced_facts {
            if else_introduced.contains(fact)
                && arms[0].facts.contains(fact)
                && arms[1].facts.contains(fact)
                && !facts.contains(fact)
            {
                facts = facts.with_fact(fact.clone());
                common_added_facts.push(fact.clone());
                for surface in then_replay.surface_propositions.surfaces(fact) {
                    if else_replay
                        .surface_propositions
                        .surfaces(fact)
                        .any(|candidate| candidate == surface)
                    {
                        execution
                            .replay
                            .surface_propositions
                            .record_lowering(surface, fact)?;
                    }
                }
            }
        }
        let mut unfolded_predicates = parent_unfolds.clone();
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            unfolded_predicates.insert(name.clone());
        }
        let step = SimpleProofStep::If {
            condition: surface_condition,
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        };
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts,
            unfolded_predicates,
            step,
        })
    }

    /// The merge law for a checked two-arm execution join: verifies both
    /// arms reached the shared continuation with identical C states and
    /// matching condition polarity, re-applies each arm's introduction
    /// deltas on the parent context, and produces the continuation context
    /// plus the structured `Branch` step. Callers assemble the successor.
    #[allow(clippy::too_many_arguments)]
    fn merge_checked_execution_join(
        &self,
        parent_facts: &ProofFacts,
        parent_unfolds: &PersistentOrderedSet<String>,
        parent_execution: &ExecutionProofState,
        statement_index: usize,
        continuation_index: usize,
        continuation_remaining: Option<Arc<CStatement>>,
        execution_start_state: CState,
        initial_continuation_depth: usize,
        require_empty: bool,
        arms: [CheckedExecutionJoinArm<'_>; 2],
    ) -> Result<CheckedExecutionJoinParts, ClickError> {
        for (name, expected, arm) in [("then", true, &arms[0]), ("else", false, &arms[1])] {
            if require_empty && !arm.certificate.steps().is_empty() {
                return Err(self.step_error(format!(
                    "cannot use the empty execution join for a nonempty {name} arm"
                )));
            }
            let replay = &arm.execution.replay;
            if !replay.completed_branch_regions.contains(&statement_index)
                || replay.frontier.continuations.len() > initial_continuation_depth
                || replay.frontier.next_statement_index != continuation_index
            {
                return Err(self.step_error(format!(
                    "{name} branch arm has not reached its shared continuation"
                )));
            }
            self.validate_execution_join_arm_deltas("join", name, expected, arm, parent_execution)?;
        }
        let then_state = &arms[0].execution.state;
        let else_state = &arms[1].execution.state;
        if **then_state != **else_state {
            return Err(self.step_error("execution `branch` arms reached different C states"));
        }
        let continuation_remaining = continuation_remaining.ok_or_else(|| {
            self.step_error("execution `branch` has no shared continuation statement")
        })?;
        let then_replay = &arms[0].execution.replay;
        let else_replay = &arms[1].execution.replay;
        let mut execution = parent_execution.clone();
        execution.has_empty_execution_branch_leaf |= arms
            .iter()
            .any(|arm| arm.execution.has_empty_execution_branch_leaf);
        self.merge_branch_surface_facts(
            &mut execution,
            parent_execution,
            [arms[0].execution, arms[1].execution],
        )?;
        execution.state = (**then_state).clone().into();
        execution.replay.completed_branch_regions.clear();
        execution
            .replay
            .completed_branch_regions
            .insert(statement_index);
        execution.replay.frontier.next_statement_index = continuation_index;
        execution.replay.frontier.execution_start_state = Some(execution_start_state);
        execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: continuation_remaining,
        };
        execution.replay.has_structured_branch_history = true;
        execution.replay.next_opaque_call = then_replay
            .next_opaque_call
            .max(else_replay.next_opaque_call);
        execution.replay.next_kernel_variable = then_replay
            .next_kernel_variable
            .max(else_replay.next_kernel_variable);
        for effect in arms[0]
            .introduced_effect_facts
            .iter()
            .chain(&arms[1].introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in arms[0]
            .introduced_prerequisites
            .iter()
            .chain(&arms[1].introduced_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in arms[0]
            .introduced_derivations
            .iter()
            .chain(&arms[1].introduced_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            if !execution.replay.unfolded_predicates.contains(name) {
                execution.replay.unfolded_predicates.push(name.clone());
            }
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path.clear();
        execution.replay.case_assumptions.clear();
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_point_state(
            &mut execution.replay,
            context.function_block,
            statement_index,
            ProgramPointKind::Exit,
            (**then_state).clone(),
        );
        record_current_statement_entry(
            &mut execution.replay,
            &execution.state,
            context.function_block,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "branch",
        )?;

        let mut facts = parent_facts.clone();
        let mut common_added_facts = Vec::new();
        let else_introduced: std::collections::BTreeSet<&Proposition> =
            arms[1].introduced_facts.iter().collect();
        for fact in &arms[0].introduced_facts {
            if else_introduced.contains(fact)
                && arms[0].facts.contains(fact)
                && arms[1].facts.contains(fact)
                && !facts.contains(fact)
            {
                facts = facts.with_fact(fact.clone());
                common_added_facts.push(fact.clone());
                for surface in then_replay.surface_propositions.surfaces(fact) {
                    if else_replay
                        .surface_propositions
                        .surfaces(fact)
                        .any(|candidate| candidate == surface)
                    {
                        execution
                            .replay
                            .surface_propositions
                            .record_lowering(surface, fact)?;
                    }
                }
            }
        }
        let mut unfolded_predicates = parent_unfolds.clone();
        for name in arms[0]
            .introduced_unfolds
            .iter()
            .chain(&arms[1].introduced_unfolds)
        {
            unfolded_predicates.insert(name.clone());
        }
        let [then_arm, else_arm] = arms;
        let step = SimpleProofStep::Branch {
            ensuring: None,
            then_proof: Box::new(then_arm.certificate),
            else_proof: Box::new(else_arm.certificate),
        };
        Ok(CheckedExecutionJoinParts {
            execution,
            facts,
            common_added_facts,
            unfolded_predicates,
            step,
        })
    }

    /// Joins the two sibling execution frontier goals created by
    /// [`Proof::split_focused_execution_branch`] at their shared
    /// continuation. Both recorded arms must be open frontier goals that
    /// reached the continuation; the interleaved steps since the split
    /// marker are partitioned into per-arm certificates by recorded
    /// attribution, each arm's introduction deltas are recovered by suffix
    /// walks against the split-time bases, and the parent obligation
    /// resumes under its original id with the merged continuation context.
    pub(super) fn join_focused_execution_branch(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        self.join_focused_execution_checked(record, false)
    }

    fn join_focused_execution_checked(
        &self,
        record: &ExecutionSplit<'a>,
        require_empty: bool,
    ) -> Result<Self, ClickError> {
        let (ids, selection, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_checked_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            record.continuation_remaining.clone(),
            record.execution_start_state.clone(),
            record.initial_continuation_depth,
            require_empty,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, selection, parts)
    }

    /// Joins the two sibling execution frontier goals created by
    /// [`Proof::split_focused_execution_branch`] when both arms completed
    /// at function exit: distinct return outcomes remain as separate paths
    /// under a logical `If`, and the parent obligation resumes at function
    /// exit under its original id.
    pub(super) fn join_focused_execution_terminal(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        let (ids, selection, arms) = self.sibling_execution_arm_views(record)?;
        let parts = self.merge_terminal_execution_join(
            &record.parent_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.statement_index,
            record.execution_start_state.clone(),
            record.initial_continuation_depth,
            None,
            arms,
        )?;
        self.resume_parent_after_sibling_join(record, ids, selection, parts)
    }

    /// Joins the two terminal arms of a proof-level execution `if`. For a
    /// preceding multi-successor call, the call remains the parent provenance
    /// node; for a fresh logical split, both arms retain the same checked C
    /// root. In either case this adds only the proof `if` and its arm bodies.
    pub(super) fn join_focused_execution_if_terminal(
        &self,
        record: &ExecutionProofCaseSplit<'a>,
    ) -> Result<Self, ClickError> {
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, record.ids)?;
        let (selection, then_view) = self.sibling_execution_arm_view_from_bases(
            "then",
            record.split,
            record.ids[0],
            then_steps,
            &record.base_facts[0],
            &record.common_facts,
            &record.base_executions[0],
            None,
        )?;
        let (_, else_view) = self.sibling_execution_arm_view_from_bases(
            "else",
            record.split,
            record.ids[1],
            else_steps,
            &record.base_facts[1],
            &record.common_facts,
            &record.base_executions[1],
            None,
        )?;
        let parts = self.merge_terminal_execution_join(
            &record.common_facts,
            &record.parent_unfolds,
            &record.parent_execution,
            record.parent_execution.replay.frontier.next_statement_index,
            record.execution_start_state.clone(),
            record.initial_continuation_depth,
            Some(record.surface_condition.clone()),
            [then_view, else_view],
        )?;
        self.resume_parent_after_sibling_join_from_marker(
            &record.marker,
            record.ids,
            selection,
            parts,
        )
    }

    /// Reduces the two sibling arms of an in-`Proof` execution split to the
    /// shared per-arm join view: both recorded goals must be open execution
    /// frontiers, the steps since the split marker partition by recorded
    /// attribution into per-arm body certificates, and each arm's
    /// introduction deltas are recovered by suffix walks against the
    /// recorded split-time bases.
    #[allow(clippy::type_complexity)]
    fn sibling_execution_arm_views<'v>(
        &'v self,
        record: &'v ExecutionSplit<'a>,
    ) -> Result<
        (
            [GoalId; 2],
            EffectGoalSelection,
            [CheckedExecutionJoinArm<'v>; 2],
        ),
        ClickError,
    > {
        let [Some(then_id), Some(else_id)] = record.ids else {
            return Err(self.step_error(
                "an execution `branch` with one feasible arm is a decided path, not a join",
            ));
        };
        let [then_steps, else_steps] =
            self.partition_steps_since(&record.marker, record.split, [then_id, else_id])?;
        let (selection, then_view) =
            self.sibling_execution_arm_view(record, "then", 0, then_id, then_steps)?;
        let (_, else_view) =
            self.sibling_execution_arm_view(record, "else", 1, else_id, else_steps)?;
        Ok(([then_id, else_id], selection, [then_view, else_view]))
    }

    /// Reduces one sibling arm of an in-`Proof` execution split to the
    /// shared per-arm join view: the recorded goal must be an open
    /// execution frontier, the partitioned steps become its body
    /// certificate, and its introduction deltas are recovered by suffix
    /// walks against the recorded split-time bases.
    fn sibling_execution_arm_view<'v>(
        &'v self,
        record: &'v ExecutionSplit<'a>,
        name: &str,
        arm_index: usize,
        id: GoalId,
        steps: Vec<SimpleProofStep>,
    ) -> Result<(EffectGoalSelection, CheckedExecutionJoinArm<'v>), ClickError> {
        let base_facts = record.base_facts[arm_index]
            .as_ref()
            .expect("a recorded arm id has a recorded fact base");
        let base_execution = record.base_executions[arm_index]
            .as_ref()
            .expect("a recorded arm id has a recorded execution base");
        let condition_theorem = record.condition_theorems[arm_index]
            .as_ref()
            .expect("a recorded arm id has a recorded condition theorem");
        self.sibling_execution_arm_view_from_bases(
            name,
            record.split,
            id,
            steps,
            base_facts,
            &record.parent_facts,
            base_execution,
            Some(condition_theorem),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn sibling_execution_arm_view_from_bases<'v>(
        &'v self,
        name: &str,
        split: SplitId,
        id: GoalId,
        steps: Vec<SimpleProofStep>,
        ancestry_facts: &'v ProofFacts,
        delta_facts: &'v ProofFacts,
        delta_execution: &'v ExecutionProofState,
        condition_theorem: Option<&'v Theorem>,
    ) -> Result<(EffectGoalSelection, CheckedExecutionJoinArm<'v>), ClickError> {
        let Some(Goal::Frontier(frontier)) = self.state.goals.get(id) else {
            return Err(self.step_error(format!(
                "cannot join `branch`: the {name} arm is not an open execution frontier"
            )));
        };
        let execution = frontier.context.execution.as_deref().ok_or_else(|| {
            self.step_error(format!("{name} branch arm lost its execution state"))
        })?;
        let not_descended = || {
            self.step_error(format!(
                "cannot join `branch`: the {name} arm does not descend from split {:?}",
                split
            ))
        };
        // Fact introductions are measured against the PARENT facts, not the
        // arm's split-time base: the container seeded each arm's record with
        // the prepared introduction set, so an arm's path facts count as
        // introduced and flow into its retained outcome paths. The replay
        // stores below instead diff against the arm base, matching the
        // container's empty per-arm records. The base ancestry check keeps
        // the arm honest about deriving from this exact split.
        if frontier
            .context
            .facts
            .introduced_since(ancestry_facts)
            .is_none()
        {
            return Err(not_descended());
        }
        let introduced_facts = frontier
            .context
            .facts
            .introduced_since(delta_facts)
            .ok_or_else(not_descended)?;
        let introduced_effect_facts = execution
            .replay
            .effect_facts
            .suffix_since(&delta_execution.replay.effect_facts)
            .ok_or_else(not_descended)?
            .to_vec();
        let introduced_prerequisites = execution
            .replay
            .function_entry_execution_prerequisites
            .introduced_since(
                &delta_execution
                    .replay
                    .function_entry_execution_prerequisites,
            )
            .ok_or_else(not_descended)?;
        let introduced_derivations = execution
            .replay
            .function_entry_derivations
            .introduced_since(&delta_execution.replay.function_entry_derivations)
            .ok_or_else(not_descended)?;
        let introduced_unfolds = execution
            .replay
            .unfolded_predicates
            .suffix_since(&delta_execution.replay.unfolded_predicates)
            .ok_or_else(not_descended)?
            .to_vec();
        Ok((
            frontier.selection,
            CheckedExecutionJoinArm {
                certificate: ProofCertificate::from_steps(steps),
                facts: &frontier.context.facts,
                execution,
                condition_theorem,
                introduced_facts,
                introduced_effect_facts,
                introduced_prerequisites,
                introduced_derivations,
                introduced_unfolds,
            },
        ))
    }

    /// Finishes an in-`Proof` execution split for which the kernel
    /// certified exactly one feasible arm. This is path retention, not a
    /// join: the sole sibling's evolved context becomes the continuation
    /// while a logical `If` records the checked source condition and an
    /// empty contradictory arm. The parent obligation resumes under its
    /// original id — unlike the container form, which keeps the arm's id —
    /// because the sibling form splices over the split region and enclosing
    /// attribution must keep addressing the parent.
    pub(super) fn finish_focused_execution_decided(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        let (take_then, arm_index, id) = match record.ids {
            [Some(id), None] => (true, 0usize, id),
            [None, Some(id)] => (false, 1, id),
            _ => {
                return Err(self.step_error(
                    "a decided execution branch requires exactly one kernel-feasible arm",
                ));
            }
        };
        // Both partition slots name the sole arm: every step recorded since
        // the marker must be attributed to it.
        let [mut steps, trailing] =
            self.partition_steps_since(&record.marker, record.split, [id, id])?;
        steps.extend(trailing);
        let name = if take_then { "then" } else { "else" };
        let (selection, view) =
            self.sibling_execution_arm_view(record, name, arm_index, id, steps)?;
        let step = self.merge_decided_execution_path(
            &record.parent_execution,
            record.statement_index,
            record.continuation_index,
            record.initial_continuation_depth,
            take_then,
            &view,
        )?;
        let mut execution = view.execution.clone();
        execution.branch_path = record.parent_execution.branch_path.clone();
        execution.has_empty_execution_branch_leaf = true;
        let parts = CheckedExecutionJoinParts {
            execution,
            facts: view.facts.clone(),
            common_added_facts: view.introduced_facts.clone(),
            unfolded_predicates: view.introduced_unfolds.iter().fold(
                record.parent_unfolds.clone(),
                |mut unfolds, name| {
                    unfolds.insert(name.clone());
                    unfolds
                },
            ),
            step,
        };
        self.resume_parent_after_sibling_join(record, [id, id], selection, parts)
    }

    /// Consumes both sibling arm goals and resumes the parent obligation
    /// under its original id with the merged continuation context, splicing
    /// the structured join step over the split region so step attribution
    /// stays correct for enclosing splits.
    fn resume_parent_after_sibling_join(
        &self,
        record: &ExecutionSplit<'a>,
        ids: [GoalId; 2],
        selection: EffectGoalSelection,
        parts: CheckedExecutionJoinParts,
    ) -> Result<Self, ClickError> {
        self.resume_parent_after_sibling_join_from_marker(&record.marker, ids, selection, parts)
    }

    fn resume_parent_after_sibling_join_from_marker(
        &self,
        marker: &ProofCheckpoint<'a>,
        ids: [GoalId; 2],
        selection: EffectGoalSelection,
        parts: CheckedExecutionJoinParts,
    ) -> Result<Self, ClickError> {
        let parent_goal = marker.node.focused;
        let parent_node = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `branch`: the split marker lost its root")
        })?;
        let open = self
            .state
            .goals
            .open
            .without_key(&ids[0])
            .without_key(&ids[1])
            .with_inserted(
                parent_goal,
                Goal::Frontier(FrontierGoal {
                    selection,
                    context: GoalContext {
                        facts: parts.facts,
                        unfolded_predicates: parts.unfolded_predicates,
                        execution: Some(Arc::new(parts.execution)),
                    },
                }),
            );
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: ProofGoals {
                    open,
                    next_id: self.state.goals.next_id,
                },
                added_facts: Arc::new(parts.common_added_facts.clone()),
                checked_facts: Arc::new(parts.common_added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(parent_node.clone()),
                step: Some(Arc::new(parts.step)),
                focused: parent_goal,
                depth: parent_node.depth + 1,
            }),
            focused: parent_goal,
        })
    }

    /// Focuses one recorded sibling arm and installs that arm's split-time
    /// path facts as the proof's delta. The container gave each arm proof
    /// its own `added_facts`; with siblings sharing one proof, the cursor
    /// move re-presents the delta that created the now-focused obligation
    /// so smart premise selection sees the same candidates.
    pub(super) fn focus_split_arm(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_then);
        let Some(id) = record.ids[arm_index] else {
            return Err(self.step_error(format!(
                "cannot focus the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            )));
        };
        let mut focused = self.focus(id)?;
        let path_facts = record.path_facts[arm_index]
            .clone()
            .expect("a recorded arm id has recorded path facts");
        focused.state = Arc::new(ProofState {
            locals: focused.state.locals.clone(),
            goals: focused.state.goals.clone(),
            added_facts: Arc::new(path_facts.clone()),
            checked_facts: Arc::new(path_facts),
        });
        Ok(focused)
    }

    /// Focuses one proof-level execution case. No C transition is repeated;
    /// the recorded polarity is re-presented only as the focused operation's
    /// local delta.
    pub(super) fn focus_execution_if_arm(
        &self,
        record: &ExecutionProofCaseSplit<'a>,
        take_then: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_then);
        let mut focused = self.focus(record.ids[arm_index])?;
        let path_facts = record.path_facts[arm_index].clone();
        focused.state = Arc::new(ProofState {
            locals: focused.state.locals.clone(),
            goals: focused.state.goals.clone(),
            added_facts: Arc::new(path_facts.clone()),
            checked_facts: Arc::new(path_facts),
        });
        Ok(focused)
    }

    /// Runs the narrow statement selector on this focused frontier until it
    /// reaches function exit. A nested C `if` recurses through an in-`Proof`
    /// split whose arms are focused runs of this same search; any other
    /// structural frontier is a search miss.
    pub(super) fn try_focused_execute_to_exit(&self) -> Result<Option<Self>, ClickError> {
        let mut proof = self.clone();
        loop {
            if proof.is_at_function_exit() {
                return Ok(Some(proof));
            }
            if let Some(next) = proof.try_indexed_execute_step()? {
                proof = next;
                continue;
            }
            if !proof.is_at_execution_branch()? {
                return Ok(None);
            }
            let (split, record) = proof.split_focused_execution_branch()?;
            let mut advanced = split;
            for take_then in [true, false] {
                if record.arm_id(take_then).is_none() {
                    continue;
                }
                let Some(next) = advanced
                    .focus_split_arm(&record, take_then)?
                    .try_focused_execute_to_exit()?
                else {
                    return Ok(None);
                };
                advanced = next;
            }
            proof = if record.sole_feasible_arm().is_some() {
                advanced.finish_focused_execution_decided(&record)?
            } else {
                advanced.join_focused_execution_terminal(&record)?
            };
        }
    }

    /// Validates and applies one already-expanded logical execution arm.
    ///
    /// Terminal and decided branches render one structural branch-entry
    /// `step using` (two for an empty C arm). The split already performed
    /// those transitions, so this checks the exact Surface operations against
    /// the C branch and applies only the remaining body steps to the focused
    /// sibling. No certificate is constructed or interpreted.
    fn checked_expanded_execution_arm_entry_steps(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
        surface_condition: Option<&ClickProposition>,
    ) -> Result<Vec<SimpleProofStep>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &record.parent_execution.replay,
            &record.parent_execution.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "expanded execution branch",
        )?;
        let CStatement::If {
            condition,
            then_branch,
            else_branch,
        } = statement
        else {
            return Err(self.step_error("expanded execution branch root is not a C `if`"));
        };
        let checked_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(record.statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        if surface_condition
            .is_some_and(|surface_condition| surface_condition != &checked_condition)
        {
            return Err(self.step_error(
                "expanded execution branch condition does not match the checked C branch",
            ));
        }
        let source_arm = if take_then {
            then_branch.as_ref()
        } else {
            else_branch.as_ref()
        };
        let entry_steps = 1 + usize::from(matches!(source_arm, CStatement::Skip));
        let path_condition = if take_then {
            checked_condition
        } else {
            negate_click_proposition(&checked_condition)
        };
        let mut expected = vec![SimpleProofStep::StepUsing(vec![path_condition])];
        expected.resize_with(entry_steps, || SimpleProofStep::StepUsing(Vec::new()));
        Ok(expected)
    }

    pub(super) fn focus_expanded_execution_arm_entry(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
        surface_condition: &ClickProposition,
        steps: &[SimpleProofStep],
    ) -> Result<Option<(Self, usize)>, ClickError> {
        let expected = self.checked_expanded_execution_arm_entry_steps(
            record,
            take_then,
            Some(surface_condition),
        )?;
        let entry_steps = expected.len();
        if record.arm_id(take_then).is_none() {
            // A common extracted surface tree may retain the checked entry
            // prefix for an arm that earlier path facts make unreachable on
            // this particular outcome. Validate that prefix exactly before
            // declining to apply the remaining, structurally classified
            // syntax: there is no successor Proof on which it could act.
            if !steps.is_empty() && steps.get(..entry_steps) != Some(expected.as_slice()) {
                return Err(self.step_error(format!(
                    "expanded execution infeasible {} arm does not begin with its {entry_steps} checked branch-entry step(s)",
                    if take_then { "then" } else { "else" },
                )));
            }
            return Ok(None);
        }
        if steps.get(..entry_steps) != Some(expected.as_slice()) {
            return Err(self.step_error(format!(
                "expanded execution {} arm does not begin with its {entry_steps} checked branch-entry step(s)",
                if take_then { "then" } else { "else" },
            )));
        }
        Ok(Some((
            self.focus_split_arm(record, take_then)?,
            entry_steps,
        )))
    }

    fn apply_focused_expanded_execution_arm(
        &self,
        record: &ExecutionSplit<'a>,
        take_then: bool,
        surface_condition: &ClickProposition,
        steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        let Some((proof, entry_steps)) =
            self.focus_expanded_execution_arm_entry(record, take_then, surface_condition, steps)?
        else {
            return Err(self.step_error("cannot advance an infeasible expanded execution arm"));
        };
        proof.apply_expanded_execution_steps_inner(&steps[entry_steps..])
    }

    fn apply_expanded_execution_steps_inner(
        &self,
        steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        let mut proof = self.clone();
        for step in steps {
            proof = match step {
                SimpleProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                } => proof.apply_expanded_execution_if(
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                )?,
                _ => proof.apply_step(step.clone())?,
            };
        }
        Ok(proof)
    }

    fn planned_execution_step_is_supported(step: &SimpleProofStep) -> bool {
        match step {
            SimpleProofStep::Have { .. }
            | SimpleProofStep::UnfoldPredicate(_)
            | SimpleProofStep::TransportUsing { .. }
            | SimpleProofStep::StepUsing(_) => true,
            SimpleProofStep::If {
                then_proof,
                else_proof,
                ..
            } => {
                !then_proof.steps().is_empty()
                    && !else_proof.steps().is_empty()
                    && then_proof
                        .steps()
                        .iter()
                        .all(Self::planned_execution_step_is_supported)
                    && else_proof
                        .steps()
                        .iter()
                        .all(Self::planned_execution_step_is_supported)
            }
            _ => false,
        }
    }

    fn planned_execution_steps_contain_transition(steps: &[SimpleProofStep]) -> bool {
        steps.iter().any(|step| match step {
            SimpleProofStep::StepUsing(_) => true,
            SimpleProofStep::If {
                then_proof,
                else_proof,
                ..
            } => {
                Self::planned_execution_steps_contain_transition(then_proof.steps())
                    || Self::planned_execution_steps_contain_transition(else_proof.steps())
            }
            _ => false,
        })
    }

    fn apply_planned_execution_steps_inner(
        &self,
        steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        let mut proof = self.clone();
        for step in steps {
            proof = match step {
                SimpleProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                } => proof.apply_planned_execution_if(
                    condition,
                    then_proof.steps(),
                    else_proof.steps(),
                )?,
                _ => proof.apply_step(step.clone())?,
            };
        }
        Ok(proof)
    }

    /// Applies one planner-selected whole-execution tree directly to this
    /// Proof. The generated tree is only structured Surface input: Proof
    /// validates each operation, owns every C split and join, and accepts the
    /// result only when the checked execution has reached function exit.
    pub(super) fn try_planned_execution_steps(
        &self,
        steps: &[SimpleProofStep],
    ) -> Result<Option<Self>, ClickError> {
        if steps.is_empty()
            || !steps.iter().all(Self::planned_execution_step_is_supported)
            || !Self::planned_execution_steps_contain_transition(steps)
        {
            return Ok(None);
        }
        let proof = self.apply_planned_execution_steps_inner(steps)?;
        Ok(proof.is_at_function_exit().then_some(proof))
    }

    fn apply_planned_execution_if(
        &self,
        condition: &ClickProposition,
        then_steps: &[SimpleProofStep],
        else_steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        let arm_premises = [then_steps, else_steps].map(|steps| match steps.first() {
            Some(SimpleProofStep::StepUsing(premises)) => Some(premises.clone()),
            _ => None,
        });
        if let [Some(then_premises), Some(else_premises)] = arm_premises {
            let tactic_index = match self.context.as_ref() {
                ProofContext::Execution(context) => context.tactic_index,
                _ => 0,
            };
            let collapsed = self.try_collapse_statement_successor_if(
                condition,
                [(tactic_index, then_premises), (tactic_index, else_premises)],
            )?;
            if let Some((split, record)) = collapsed {
                let advanced = split
                    .focus_execution_if_arm(&record, true)?
                    .apply_planned_execution_steps_inner(&then_steps[1..])?
                    .focus_execution_if_arm(&record, false)?
                    .apply_planned_execution_steps_inner(&else_steps[1..])?;
                return advanced.join_focused_execution_if_terminal(&record);
            }
        }
        if let Some((split, record)) = self.enter_statement_successor_if(condition)? {
            let advanced = split
                .focus_execution_if_arm(&record, true)?
                .apply_planned_execution_steps_inner(then_steps)?
                .focus_execution_if_arm(&record, false)?
                .apply_planned_execution_steps_inner(else_steps)?;
            return advanced.join_focused_execution_if_terminal(&record);
        }

        let (split, record) = self.split_focused_execution_branch()?;
        let mut advanced = split;
        for (take_then, steps) in [(true, then_steps), (false, else_steps)] {
            if record.arm_id(take_then).is_none() {
                continue;
            }
            let entry_steps = advanced
                .checked_expanded_execution_arm_entry_steps(&record, take_then, None)?
                .len();
            if steps.len() < entry_steps
                || !steps[..entry_steps]
                    .iter()
                    .all(|step| matches!(step, SimpleProofStep::StepUsing(_)))
            {
                return Err(self.step_error(format!(
                    "planned execution {} arm does not begin with its {entry_steps} C branch-entry step(s)",
                    if take_then { "then" } else { "else" },
                )));
            }
            advanced = advanced
                .focus_split_arm(&record, take_then)?
                .apply_planned_execution_steps_inner(&steps[entry_steps..])?;
        }
        advanced.join_focused_execution_split(&record, false, None)
    }

    /// Applies an already-expanded logical C branch as one audited structural
    /// Proof transition. Source syntax supplies only its condition and simple
    /// arm operations; the split, entry validation, focused successors, and
    /// join remain owned by this Proof lineage.
    pub(super) fn apply_expanded_execution_if(
        &self,
        condition: &ClickProposition,
        then_steps: &[SimpleProofStep],
        else_steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        let (split, record) = self.split_focused_execution_branch()?;
        let mut advanced = split;
        for (take_then, steps) in [(true, then_steps), (false, else_steps)] {
            if record.arm_id(take_then).is_none() {
                if !steps.is_empty() {
                    return Err(self.step_error(format!(
                        "expanded execution {} arm is nonempty, but the checked C branch is infeasible",
                        if take_then { "then" } else { "else" },
                    )));
                }
                continue;
            }
            if !matches!(
                steps.last(),
                Some(SimpleProofStep::StepUsing(_) | SimpleProofStep::If { .. })
            ) {
                return Err(self.step_error(format!(
                    "expanded execution {} arm does not end in a checked C step",
                    if take_then { "then" } else { "else" },
                )));
            }
            advanced = advanced
                .apply_focused_expanded_execution_arm(&record, take_then, condition, steps)?;
        }
        advanced.join_focused_execution_split(&record, false, None)
    }

    /// Enforces the source `branch` body's boundary on the focused sibling
    /// arm: once the arm has reached the shared continuation, further
    /// source `step using` transitions belong to the continuation, not the
    /// arm. The terminal-execution operation is unconstrained, as in the
    /// container form.
    pub(super) fn ensure_focused_arm_step(
        &self,
        record: &ExecutionSplit<'a>,
        step: &SimpleProofStep,
    ) -> Result<(), ClickError> {
        if !matches!(step, SimpleProofStep::StepUsing(_)) {
            return Ok(());
        }
        self.ensure_focused_arm_can_advance(record)
    }

    /// The unconditional form of the boundary: source transitions — explicit
    /// `step using` and the smart statement selector alike — must not
    /// consume the shared continuation from inside an arm.
    pub(super) fn ensure_focused_arm_can_advance(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<(), ClickError> {
        let Some(join) = derive_execution_join_continuation(
            &record.parent_execution,
            &record.continuation_remaining,
            record.continuation_index,
        ) else {
            return Ok(());
        };
        let Some(execution) = self.execution() else {
            return Ok(());
        };
        if execution
            .replay
            .completed_branch_regions
            .contains(&record.statement_index)
            && execution.replay.frontier.next_statement_index == join.next_statement_index
            && execution
                .replay
                .frontier
                .continuations
                .shares_tail_with(&join.continuations)
        {
            return Err(self.step_error(format!(
                "focused arm of `branch` must stop at the shared continuation statement({})",
                record.continuation_index
            )));
        }
        Ok(())
    }

    /// Preserves the original empty-arm entry point for callers that require
    /// the sibling branch region to contain no body steps.
    pub(super) fn join_focused_execution_empty(
        &self,
        record: &ExecutionSplit<'a>,
    ) -> Result<Self, ClickError> {
        self.join_focused_execution_checked(record, true)
    }

    /// True when the split recorded two feasible arms and both sibling
    /// goals completed at function exit.
    pub(super) fn split_arms_at_function_exit(&self, record: &ExecutionSplit<'a>) -> bool {
        record.sole_feasible_arm().is_none()
            && record.ids.iter().flatten().all(|id| {
                self.state
                    .goals
                    .get(*id)
                    .and_then(|goal| goal.context().execution.as_deref())
                    .is_some_and(|execution| execution.replay.is_at_function_exit())
            })
    }

    /// Selects the structural join for an advanced in-`Proof` execution
    /// split, mirroring the container's join dispatch: an explicit
    /// interface joins (or decides) through it, a sole feasible arm is
    /// decided path retention, two returned arms join terminally, and a
    /// nonterminal region joins at the shared continuation.
    pub(super) fn join_focused_execution_split(
        &self,
        record: &ExecutionSplit<'a>,
        empty: bool,
        ensuring: Option<Vec<ProofAssertion>>,
    ) -> Result<Self, ClickError> {
        if let Some(assertions) = ensuring {
            self.join_focused_execution_interface(record, assertions)
        } else if record.sole_feasible_arm().is_some() {
            self.finish_focused_execution_decided(record)
        } else if self.split_arms_at_function_exit(record) {
            self.join_focused_execution_terminal(record)
        } else if empty {
            self.join_focused_execution_empty(record)
        } else {
            self.join_focused_execution_branch(record)
        }
    }

    pub(super) fn split_focused_execution_branch(
        &self,
    ) -> Result<(Self, ExecutionSplit<'a>), ClickError> {
        let prepared = self.prepare_execution_branch()?;
        let Some(Goal::Frontier(parent)) = self.focused_goal() else {
            return Err(self.step_error("`branch` requires an open execution frontier"));
        };
        let selection = parent.selection;
        let unfolds = parent.context.unfolded_predicates.clone();
        let parent_facts = parent.context.facts.clone();
        let parent_execution = parent
            .context
            .execution
            .clone()
            .expect("the preparation requires an execution frontier");
        let split = SplitId(self.state.goals.next_id);
        let ids = [
            GoalId(self.state.goals.next_id + 1),
            GoalId(self.state.goals.next_id + 2),
        ];
        let mut open = self.state.goals.open.without_key(&self.focused);
        let mut arm_ids: [Option<GoalId>; 2] = [None, None];
        let mut condition_theorems: [Option<Theorem>; 2] = [None, None];
        let mut base_facts: [Option<ProofFacts>; 2] = [None, None];
        let mut base_executions: [Option<Arc<ExecutionProofState>>; 2] = [None, None];
        let mut path_facts: [Option<Vec<Proposition>>; 2] = [None, None];
        for (arm_index, prepared_arm) in prepared.arms.into_iter().enumerate() {
            let Some(prepared_arm) = prepared_arm else {
                continue;
            };
            arm_ids[arm_index] = Some(ids[arm_index]);
            condition_theorems[arm_index] = Some(prepared_arm.condition_theorem);
            base_facts[arm_index] = Some(prepared_arm.facts.clone());
            path_facts[arm_index] = Some(prepared_arm.path_facts);
            let execution = Arc::new(prepared_arm.execution);
            base_executions[arm_index] = Some(execution.clone());
            open = open.with_inserted(
                ids[arm_index],
                Goal::Frontier(FrontierGoal {
                    selection,
                    context: GoalContext {
                        facts: prepared_arm.facts,
                        unfolded_predicates: unfolds.clone(),
                        execution: Some(execution),
                    },
                }),
            );
        }
        let focused = arm_ids
            .iter()
            .flatten()
            .next()
            .copied()
            .expect("the preparation rejects branches with no feasible arm");
        let first_path_facts = path_facts
            .iter()
            .flatten()
            .next()
            .cloned()
            .expect("a feasible arm records its path facts");
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals: ProofGoals {
                    open,
                    next_id: self.state.goals.next_id + 3,
                },
                // The successor starts focused on the first feasible arm and
                // carries that arm's path facts as its delta, exactly as the
                // container's arm proof did; `focus_split_arm` installs the
                // matching delta when the driver moves to the other arm.
                added_facts: Arc::new(first_path_facts.clone()),
                checked_facts: Arc::new(first_path_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused,
        };
        let record = ExecutionSplit {
            marker: successor.checkpoint(),
            split,
            ids: arm_ids,
            condition_theorems,
            base_facts,
            base_executions,
            path_facts,
            parent_facts,
            parent_unfolds: unfolds,
            parent_execution,
            statement_index: prepared.statement_index,
            continuation_index: prepared.continuation_index,
            continuation_remaining: prepared.continuation_remaining,
            execution_start_state: prepared.execution_start_state,
            initial_continuation_depth: prepared.initial_continuation_depth,
        };
        Ok((successor, record))
    }

    fn certificate_after_node(
        &self,
        ancestor: Option<&Arc<ProofNode>>,
    ) -> Result<ProofCertificate, ClickError> {
        let expected_depth = ancestor.map_or(0, |node| node.depth);
        let mut steps = Vec::with_capacity(self.node.depth.saturating_sub(expected_depth));
        let mut node = Some(self.node.clone());
        while let Some(current) = node {
            if ancestor.is_some_and(|ancestor| Arc::ptr_eq(ancestor, &current)) {
                steps.reverse();
                return Ok(ProofCertificate::from_steps(steps));
            }
            if let Some(step) = &current.step {
                steps.push(step.as_ref().clone());
            }
            node = current.parent.clone();
        }
        if ancestor.is_some() {
            return Err(self.step_error("certificate checkpoint is not an ancestor of this proof"));
        }
        steps.reverse();
        Ok(ProofCertificate::from_steps(steps))
    }

    fn lower_surface_proposition(
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
                lower_pure_theorem_proposition(
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
                })
            }
            ProofContext::Point(context) => {
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                if let Some(recorded) = context
                    .surface_propositions
                    .available_kernel(&surface, context.lowering_context.as_ref())
                {
                    return Ok(recorded.clone());
                }
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.program_point_states,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            // A judgment carrying outcome point data lowers result-aware:
            // `result` and outcome-anchored forms resolve against the
            // outcome's own state, recorded lowerings, and return value.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view()
                    .expect("a focused outcome judgment resolves its point view");
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                if let Some(recorded) = view
                    .surface_propositions
                    .available_kernel_matching(&surface, |kernel| self.facts().contains(kernel))
                {
                    return Ok(recorded.clone());
                }
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.program_point_states,
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
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                let pre_state = execution.replay.old_reference_state(&execution.state);
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parsed_function.parameters(),
                    context.arguments,
                    pre_state,
                    &execution.state,
                    None,
                    &execution.replay.program_point_states,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
        }
    }

    /// Lowers a surface proposition at this Proof's actual semantic point,
    /// without accepting a historical Surface-to-kernel index entry as a
    /// substitute for an in-scope form.
    ///
    /// The ordinary checker may use that index to recognize an exact fact.
    /// Smart theorem selection additionally needs arguments that can be
    /// lowered when the retained `apply` step runs. In particular, a local
    /// that has left scope must be written through `at(...)` rather than
    /// merely associated with an indexed historical fact.
    fn lower_surface_proposition_direct(
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
            ProofContext::Point(context) => {
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.program_point_states,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            ProofContext::Execution(context) => {
                let execution = self.execution().ok_or_else(|| {
                    self.step_error("execution proposition proof lost its semantic frontier")
                })?;
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                let pre_state = execution.replay.old_reference_state(&execution.state);
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parsed_function.parameters(),
                    context.arguments,
                    pre_state,
                    &execution.state,
                    None,
                    &execution.replay.program_point_states,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
        }
    }

    /// Lowers a newly stated proof goal at the current semantic point.
    ///
    /// Fact references may deliberately resolve through a recorded surface
    /// form, but a new goal may not: the same form can name facts
    /// retained from an older snapshot. Selecting such a fact here would let
    /// `have P by assumption` check one kernel proposition and serialize a
    /// surface `P` that independently lowers to another.
    fn lower_surface_goal(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.lower_surface_proposition(surface, description),
            ProofContext::Point(context) => {
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    context.parameters,
                    context.arguments,
                    context.pre_state,
                    context.state,
                    context.result,
                    context.program_point_states,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            // A judgment stated at a function outcome lowers strictly at
            // that outcome: like the point arm above, this deliberately
            // skips the recorded-lowering shortcut so a newly stated goal
            // cannot borrow a same-written fact's older snapshot anchoring.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view()
                    .expect("a focused outcome judgment resolves its point view");
                let surface = self.substitute_point_locals_in_proposition(surface)?;
                lower_point_proposition_with_assumptions(
                    &surface,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.program_point_states,
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
    fn point_local_substitutions(
        &self,
        names: impl IntoIterator<Item = String>,
    ) -> BTreeMap<String, ContractExpression> {
        let surface_bindings = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => Some(&goal.surface_bindings),
            _ => None,
        };
        names
            .into_iter()
            .filter_map(|name| {
                surface_bindings
                    .and_then(|bindings| bindings.get(&name))
                    .or_else(|| self.state.locals.values.get(&name))
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect()
    }

    fn substitute_point_locals_in_proposition(
        &self,
        proposition: &ClickProposition,
    ) -> Result<ClickProposition, ClickError> {
        let mut names = BTreeSet::new();
        collect_click_proposition_referenced_names(proposition, &mut names);
        let substitutions = self.point_local_substitutions(names);
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
    fn substitute_goal_surface_bindings_in_proposition(
        &self,
        proposition: &ClickProposition,
    ) -> Result<ClickProposition, ClickError> {
        let Some(Goal::Proposition(goal)) = self.focused_goal() else {
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

    fn substitute_point_locals_in_expression(
        &self,
        expression: &ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        let names = contract_expression_referenced_names(expression);
        let substitutions = self.point_local_substitutions(names);
        if substitutions.is_empty() {
            return Ok(expression.clone());
        }
        substitute_contract_expression(expression, &substitutions).map_err(|message| {
            self.step_error(format!("could not substitute proof locals: {message}"))
        })
    }

    fn apply_predicate_unfold(&self, name: &String) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => self.apply_proposition_predicate_unfold(
                name,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                self.node.depth,
            ),
            ProofContext::Point(context) => self.apply_proposition_predicate_unfold(
                name,
                context.predicate_environment,
                context.click_function_environment,
                context.claim_label,
                context.tactic_index,
            ),
            // A function-outcome goal unfolds its own path-local facts and
            // delta only: the borrowed execution snapshot is shared by every
            // sibling outcome and must not absorb one path's unfolding.
            ProofContext::Execution(context) if self.focused_outcome_point().is_some() => self
                .apply_proposition_predicate_unfold(
                    name,
                    context.predicate_environment,
                    context.click_function_environment,
                    context.claim_label,
                    context.tactic_index,
                ),
            ProofContext::Execution(_) => self.apply_execution_unfold(name),
        }
    }

    fn apply_proposition_predicate_unfold(
        &self,
        name: &String,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        claim_label: &str,
        tactic_index: usize,
    ) -> Result<ProofState, ClickError> {
        let checked = check_unfold_predicate_in_facts(
            &self.facts(),
            name,
            predicate_environment,
            click_function_environment,
            claim_label,
            tactic_index,
        )?;
        let goal = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => {
                let surface = match &goal.surface {
                    Some(surface) => Some(
                        unfold_structural_invariant_proposition(
                            predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))?,
                    ),
                    None => None,
                };
                // Point and outcome certificates replay `unfold` from its
                // retained surface form.  Re-lower that unfolded body
                // against the checked successor facts as part of this same
                // audited step, so resource counts and current memory loads
                // resolve exactly as they do during independent replay.
                // Unfolding only the already-lowered kernel predicate leaves
                // those expressions stranded in the older lowering context.
                let kernel = match (&surface, self.context.as_ref()) {
                    (Some(surface), ProofContext::Point(context)) => {
                        let surface = self.substitute_point_locals_in_proposition(surface)?;
                        lower_point_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            context.parameters,
                            context.arguments,
                            context.pre_state,
                            context.state,
                            context.result,
                            context.program_point_states,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .map_err(|message| self.step_error(message))?
                    }
                    (Some(surface), ProofContext::Execution(_))
                        if self.focused_outcome_point().is_some() =>
                    {
                        let view = self
                            .outcome_point_view()
                            .expect("a focused outcome judgment resolves its point view");
                        let surface = self.substitute_point_locals_in_proposition(surface)?;
                        lower_point_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            view.parameters,
                            view.arguments,
                            view.pre_state,
                            view.state,
                            view.result,
                            view.program_point_states,
                            view.predicate_environment,
                            view.click_function_environment,
                        )
                        .map_err(|message| self.step_error(message))?
                    }
                    _ => unfold_predicates_in_proposition(
                        predicate_environment,
                        click_function_environment,
                        std::slice::from_ref(name),
                        &goal.kernel,
                        checked.facts.assumptions(),
                    )
                    .map_err(|message| self.step_error(message))?,
                };
                self.refined_proposition(
                    self.refined_context(checked.facts.clone()),
                    kernel,
                    surface,
                )
            }
            Some(goal @ (Goal::Frontier(_) | Goal::FunctionOutcome(_))) => {
                let mut unfolded = goal.context().unfolded_predicates.clone();
                unfolded.insert(name.clone());
                goal.with_context(GoalContext {
                    facts: checked.facts.clone(),
                    unfolded_predicates: unfolded,
                    execution: goal.context().execution.clone(),
                })
            }
            None => return Err(self.step_error("`unfold` requires an open goal")),
        };
        let goal = {
            let mut unfolded = goal.context().unfolded_predicates.clone();
            unfolded.insert(name.clone());
            goal.with_context(GoalContext {
                facts: goal.context().facts.clone(),
                unfolded_predicates: unfolded,
                execution: goal.context().execution.clone(),
            })
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            goals: self.state.goals.replace_at(self.focused, goal),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_execution_unfold(&self, name: &String) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`unfold` requires an execution-frontier proof"));
        };
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let checked = check_unfold_predicate_facts(
            &mut execution.replay,
            &execution.state,
            &self.facts(),
            name,
            context.function,
            context.arguments,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        let mut unfolded_predicates = self.focused_goal_unfolds().clone();
        for name in &checked.added_unfolded_predicates {
            unfolded_predicates.insert(name.clone());
        }
        let refined_goal = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => {
                let surface = goal
                    .surface
                    .as_deref()
                    .map(|surface| {
                        unfold_structural_invariant_proposition(
                            context.predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))
                    })
                    .transpose()?;
                let kernel = match &surface {
                    Some(surface) => {
                        let surface = self.substitute_point_locals_in_proposition(surface)?;
                        let pre_state = execution.replay.old_reference_state(&execution.state);
                        lower_point_proposition_with_assumptions(
                            &surface,
                            checked.facts.assumptions(),
                            context.parsed_function.parameters(),
                            context.arguments,
                            pre_state,
                            &execution.state,
                            None,
                            &execution.replay.program_point_states,
                            context.predicate_environment,
                            context.click_function_environment,
                        )
                        .map_err(|message| {
                            self.step_error(format!("could not unfold proposition goal: {message}"))
                        })?
                    }
                    None => unfold_predicates_in_proposition(
                        context.predicate_environment,
                        context.click_function_environment,
                        std::slice::from_ref(name),
                        &goal.kernel,
                        checked.facts.assumptions(),
                    )
                    .map_err(|message| self.step_error(message))?,
                };
                Some((kernel, surface))
            }
            _ => None,
        };
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_function_entry_prerequisites,
            function_entry_derivations: checked.added_function_entry_derivations,
            unfolded_predicates: checked.added_unfolded_predicates,
            statement_partition: None,
        };
        let goal_context = GoalContext {
            facts: checked.facts,
            unfolded_predicates,
            execution: Some(Arc::new(execution)),
        };
        let goal = match refined_goal {
            Some((kernel, surface)) => self.refined_proposition(goal_context, kernel, surface),
            None => self
                .focused_goal()
                .expect("execution unfold requires an open goal")
                .with_context(goal_context),
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            // A nested proposition proof stated at this frontier unfolds its
            // own goal through the same checked operation. Other execution
            // goals retain their kind while installing the updated snapshot
            // and unfold delta.
            goals: self.state.goals.replace_at(self.focused, goal),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_execution_resource_observation(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`observe` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`observe`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(
                self.step_error("`observe` must run before execution reaches function exit")
            );
        }
        let checked = observe_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.state).clone(),
            self.facts().clone(),
            &mut execution.replay.surface_propositions,
            &mut execution.replay.function_entry_derivations,
            &mut execution.replay.function_entry_execution_prerequisites,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.state = checked.state.into();
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_certification_facts,
            function_entry_derivations: checked.added_derivations,
            unfolded_predicates: Vec::new(),
            statement_partition: None,
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .replace_frontier_at(self.focused, checked.facts, execution),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_execution_resource_unfold(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource `unfold` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("resource `unfold`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(self
                .step_error("resource `unfold` must run before execution reaches function exit"));
        }
        let checked = unfold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.state).clone(),
            self.facts().clone(),
            &mut execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution.state = checked.state.into();
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .replace_frontier_at(self.focused, checked.facts, execution),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_execution_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("resource `fold` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("resource `fold`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.replay.is_at_function_exit() {
            return Err(
                self.step_error("resource `fold` must run before execution reaches function exit")
            );
        }
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        let checked = fold_composite_resource_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            context.tactic_index,
            self.facts().clone(),
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            (*execution.state).clone(),
            context.predicate_environment,
            context.click_function_environment,
            &execution.replay.unfolded_predicates,
        )?;
        execution.state = checked.state.into();
        execution.replay.has_resource_surface_history = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .replace_frontier_at(self.focused, checked.facts, execution),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Applies one source-ordered composite fold to the focused typed outcome.
    /// The result/state snapshot and persistent fact root advance together in
    /// the returned Proof successor; no caller-owned outcome is mutated.
    fn apply_outcome_resource_fold(
        &self,
        resource: &ResourceClause,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("outcome resource `fold` requires an execution proof"));
        };
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("outcome resource `fold` requires a focused outcome goal"));
        };
        let execution = goal.context.execution.as_deref().ok_or_else(|| {
            self.step_error("outcome resource `fold` lost its execution snapshot")
        })?;
        let pre_state = execution.replay.execution_start_state(&execution.state);
        let outcome = CFunctionOutcome::Return {
            value: (*goal.point.result).clone(),
            state: (*goal.point.state).clone(),
        };
        let checked = fold_composite_resource_on_outcome_for_proof(
            context.resource_environment,
            resource,
            context.claim_label,
            goal.path_index,
            &goal.point.execution_pure_facts,
            self.facts().clone(),
            &goal.point.surface_propositions,
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            outcome,
            context.predicate_environment,
            context.click_function_environment,
            &self.active_unfolded_predicates(),
        )?;
        let CFunctionOutcome::Return { value, state } = checked.outcome else {
            unreachable!("folding a return outcome preserves its outcome kind")
        };
        let mut point = (*goal.point).clone();
        point.result = Arc::new(value);
        point.state = state.into();
        let mut updated = goal.clone();
        updated.point = Arc::new(point);
        updated.context.facts = checked.facts;
        Ok(ProofState {
            locals: self.state.locals.clone(),
            goals: self
                .state
                .goals
                .replace_at(self.focused, Goal::FunctionOutcome(updated)),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    pub(super) fn into_execution_context(self) -> Result<ProofReplayContext, ClickError> {
        #[cfg(test)]
        EXECUTION_CONTEXT_EXPORTS.with(|exports| exports.set(exports.get() + 1));
        #[cfg(test)]
        COLLECTED_EXECUTION_CONTEXT_EXPORT_LABELS.with(|labels| {
            if let Some(labels) = labels.borrow_mut().as_mut() {
                labels.push(self.context.claim_label().to_string());
            }
        });
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("proof does not own an execution frontier"));
        }
        let missing = format!(
            "`{}` proof step {}: execution-frontier successor lost its semantic state",
            self.context.claim_label(),
            self.node.depth
        );
        // This is a legacy compatibility/export boundary, not a semantic
        // transition. A smart tactic may legitimately retain any ancestor or
        // successor; materializing the selected checked state must therefore
        // not require unique ownership of the Proof.
        let execution = self
            .goal_execution()
            .cloned()
            .ok_or_else(|| ClickError::new(missing))?;
        let execution = Arc::unwrap_or_clone(execution);
        Ok(ProofReplayContext {
            state: execution.state.into_value(),
            pure_facts: self.facts().to_vec(),
            replay: Box::new(execution.replay),
            branch_path: execution.branch_path,
        })
    }

    /// Borrows the terminal execution data needed by claim finalization
    /// without exporting it into a mutable replay context.
    pub(super) fn finalization_view(&self) -> Result<ProofFinalizationView<'_>, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("proof does not own an execution frontier"));
        }
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        Ok(ProofFinalizationView {
            state: &execution.state,
            facts: self.facts().to_vec(),
            replay: &execution.replay,
            branch_path: &execution.branch_path,
            outcome_branch_decisions: execution.outcome_branch_decisions.as_ref(),
        })
    }

    /// Records one source-ordered outcome operation on this terminal Proof.
    /// This is cursor metadata only: the operation's semantic transition is
    /// applied later to each typed `FunctionOutcome` goal by finalization.
    /// When expansion selected this source occurrence, the retained prefix is
    /// serialized solely to seed that requested capture.
    pub(super) fn defer_post_execution_source_tactic(
        &self,
        tactic_index: usize,
        source_index: usize,
        tactic: PostExecutionTactic,
        expansion_capture: Option<&mut ExpansionCapture>,
    ) -> Result<Self, ClickError> {
        self.require_execution_frontier("post-execution tactic scheduling")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution proof lost its terminal state"))?;
        if !execution.replay.is_at_function_exit() {
            return Err(
                self.step_error("post-execution tactics can be scheduled only at function exit")
            );
        }
        if begin_tactic_expansion_capture(expansion_capture, source_index, &execution.replay) {
            execution.replay.deferred_tactic_capture = Some(DeferredTacticCapture {
                tactic_index,
                source_index,
                post_execution_index: execution.replay.post_execution_tactics.len(),
                branch_skeleton: ProofCertificate::from_steps(surface_branch_skeleton(
                    self.certificate().steps(),
                ))
                .to_proof_tactics(),
            });
        }
        execution
            .replay
            .defer_post_execution(tactic_index, source_index, tactic);
        let mut state = (*self.state).clone();
        state.goals =
            state
                .goals
                .replace_execution_at(self.focused, self.facts().clone(), execution);
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(state),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Semantic facts introduced by the most recently accepted step.
    /// Enclosing proof infrastructure can incorporate this output-sensitive
    /// delta without traversing or cloning the proof's complete fact set.
    pub(super) fn added_facts(&self) -> &[Proposition] {
        self.state.added_facts.as_ref()
    }

    /// Exact semantic facts selected or established by the latest step, in
    /// step-defined order. This lets enclosing surface bookkeeping record the
    /// checker-owned forms without re-lowering them.
    pub(super) fn checked_facts(&self) -> &[Proposition] {
        self.state.checked_facts.as_ref()
    }

    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// sole nonterminal move and strictly removes one outer goal connective.
    ///
    /// A miss is `Ok(None)` and leaves `self` the unchanged authority. An
    /// error is a tooling failure such as an exceeded deadline; it must abort
    /// the enclosing search rather than read as one more rejection.
    pub(super) fn try_direct_logical_closure(&self) -> Result<Option<Self>, ClickError> {
        let mut budget = attempt::AttemptBudget::unbounded();
        let mut proof = self.clone();
        loop {
            if let Some(closed) = attempt::try_steps(
                &proof,
                &mut budget,
                [
                    SimpleProofStep::Normalize,
                    SimpleProofStep::Assumption,
                    SimpleProofStep::Split,
                    SimpleProofStep::Left,
                    SimpleProofStep::Right,
                    SimpleProofStep::Enumerate,
                ],
            )? {
                return Ok(Some(closed));
            }
            match attempt::candidate_outcome(proof.apply_step(SimpleProofStep::Intro))? {
                Some(introduced) => proof = introduced,
                None => return Ok(None),
            }
        }
    }

    /// Searches the currently migrated `simp` vocabulary against this proof.
    ///
    /// Direct logical closers remain the cheap first choice. For a pure or
    /// point signed-order/equality derivation, the kernel-selected edge path
    /// is translated into a candidate made only of checked theorem
    /// applications, rewrites, and nested `have` scopes. The candidate
    /// advances this same `Proof`; no semantic result is produced before
    /// those simple steps have been accepted.
    pub(super) fn try_simp_closure(&self) -> Result<Option<Self>, ClickError> {
        if let Some(proof) = self.try_direct_logical_closure()? {
            return Ok(Some(proof));
        }
        self.try_simp_closure_after_direct(false)
    }

    /// Continues smart closure after direct logical candidates have either
    /// missed or been deliberately rejected as non-replayable. When
    /// `exclude_exact_goal` is true, the atomic derivation query may not cite
    /// the goal's own ambient fact; every selected theorem step is still
    /// checked against this unchanged Proof.
    fn try_simp_closure_after_direct(
        &self,
        exclude_exact_goal: bool,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_selected_unchanged_load_forall_goal(surface_goal, &[])
        {
            return Ok(Some(proof));
        }
        let atomic = (|| {
            let (goal, derivation, premise_pairs, point_application_closes_goal) =
                self.selected_simp_derivation(exclude_exact_goal)?;
            self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                &premise_pairs,
                point_application_closes_goal,
            )
            .or_else(|| self.try_selected_equality_rewrite_chain(&premise_pairs))
            .or_else(|| self.try_selected_predecessor_upper_bound(&goal, &premise_pairs))
            .or_else(|| {
                self.surface_goal().and_then(|surface_goal| {
                    self.try_selected_unchanged_load_forall_goal(surface_goal, &premise_pairs)
                        .or_else(|| {
                            self.try_selected_forall_goal(&goal, surface_goal, &premise_pairs)
                        })
                })
            })
            .or_else(|| self.try_selected_forall_instantiation(&goal, &premise_pairs))
            .or_else(|| self.try_selected_disjunction_cases(&premise_pairs))
        })();
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
        }
        let anchored_pairs = self
            .selected_simp_derivation(exclude_exact_goal)
            .map(|(_, _, pairs, _)| pairs)
            .unwrap_or_default();
        if let Some(anchored) = self
            .try_outcome_anchored_order_transitivity(&anchored_pairs)
            .or_else(|| self.try_outcome_anchored_increment_order(&anchored_pairs))
        {
            return Ok(Some(anchored));
        }
        if let Some(rewritten) = self.try_indexed_goal_equality_rewrite_closure() {
            return Ok(Some(rewritten));
        }
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_outcome_snapshot_transport_closure(surface_goal)?
        {
            return Ok(Some(proof));
        }
        if let Some(instantiated) = self.try_indexed_forall_instantiation() {
            return Ok(Some(instantiated));
        }
        // The atomic helpers still classify their internal candidate misses
        // as `Option`; surface a deadline that fired inside them here rather
        // than continuing into structural search with it exceeded.
        check_verification_deadline()?;
        let Some(surface_goal) = self.surface_goal().cloned() else {
            return Ok(None);
        };
        self.try_structural_simp_closure(&surface_goal)
    }

    /// Proves a two-edge non-strict outcome bound at the return entry or its
    /// immediate predecessor. Outcome lowering deliberately keeps selected
    /// premises in their source form; anchoring those exact premises at
    /// the execution boundary lets the ordinary theorem checker connect a
    /// returned local to its result without consulting the retired planner.
    fn try_outcome_anchored_order_transitivity(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let point = self.focused_outcome_point()?;
        let anchor = point.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let ordered = premise_pairs
                .iter()
                .filter_map(|(_, surface)| {
                    let anchored = surface_with_source_site(surface, anchor).ok()?;
                    let parts = surface_nonstrict_parts(&anchored)?;
                    Some((anchored, parts))
                })
                .collect::<Vec<_>>();
            for (first_surface, (first, middle)) in &ordered {
                for (second_surface, (second_middle, last)) in &ordered {
                    if middle != second_middle {
                        continue;
                    }
                    let theorem = SimpleProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_ge_transitive".to_string(),
                            arguments: vec![last.clone(), middle.clone(), first.clone()],
                        },
                        premises: vec![second_surface.clone(), first_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Proves an outcome increment bound at the return entry or its immediate
    /// predecessor. The latter is the assignment boundary that can connect a
    /// named return local to the increment expression. The two propositions
    /// come only from the atomic derivation's selected requirements; the
    /// ordinary theorem, nested-`have`, and assumption checkers decide whether
    /// either constant-size historical application establishes the current
    /// result-aware goal.
    fn try_outcome_anchored_increment_order(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let point = self.focused_outcome_point()?;
        let anchor = point.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        let surface_goal = self.surface_goal()?.clone();
        if surface_nonstrict_parts(&surface_goal).is_none() {
            return None;
        }
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let mut lower_bounds = Vec::new();
            let mut upper_bounds = Vec::new();
            for (_, surface) in premise_pairs {
                let anchored = surface_with_source_site(surface, anchor).ok()?;
                if let Some(parts) = surface_nonstrict_parts(&anchored) {
                    lower_bounds.push((anchored.clone(), parts));
                }
                if let Some(parts) = surface_strict_parts(&anchored) {
                    upper_bounds.push((anchored, parts));
                }
            }
            for (lower_surface, (surface_lower, lower_value)) in &lower_bounds {
                for (upper_surface, (upper_value, surface_upper)) in &upper_bounds {
                    if lower_value != upper_value {
                        continue;
                    }
                    let theorem = SimpleProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "int32_increment_preserves_order".to_string(),
                            arguments: vec![
                                lower_value.clone(),
                                surface_lower.clone(),
                                surface_upper.clone(),
                            ],
                        },
                        premises: vec![lower_surface.clone(), upper_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    let one = ContractExpression::CFragment(CExpression::Value(int32(1)));
                    let theorem_conclusion = ClickProposition::Comparison {
                        left: ContractExpression::Add(
                            Box::new(surface_lower.clone()),
                            Box::new(one.clone()),
                        ),
                        operator: ComparisonOperator::LessEqual,
                        right: ContractExpression::Add(
                            Box::new(lower_value.clone()),
                            Box::new(one),
                        ),
                    };
                    if let Some(closed) = applied
                        .apply_step(SimpleProofStep::TransportUsing {
                            source: theorem_conclusion,
                            target: surface_goal.clone(),
                            premises: Vec::new(),
                        })
                        .ok()
                        .or_else(|| applied.try_direct_logical_closure().ok().flatten())
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Tries the focused outcome goal itself as one explicit fact transport
    /// from a recorded program point. The candidate space is the execution's
    /// program-point index, not the ambient fact set; every accepted source
    /// and target is checked by `TransportUsing` on this immutable Proof.
    fn try_outcome_snapshot_transport_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(view) = self.outcome_point_view() else {
            return Ok(None);
        };
        if let Some(source) = old_reflexive_transport_source(surface_goal) {
            match self.search_point_fact_transport(&source, surface_goal, std::iter::empty()) {
                Ok(proof) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        let entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let selectors =
            std::iter::once(entry).chain(view.program_point_states.keys().rev().cloned());
        let mut tried = BTreeSet::new();
        for point in selectors {
            if !tried.insert(point.clone()) {
                continue;
            }
            let source = ClickProposition::At {
                selector: VisitSelector::ProgramPoint(point),
                proposition: Box::new(surface_goal.clone()),
            };
            match self.search_point_fact_transport(
                &source,
                surface_goal,
                std::iter::once(source.clone()),
            ) {
                Ok(proof) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        Ok(None)
    }

    /// Refines the Proof-owned Surface goal through audited scopes and steps.
    /// The caller cannot supply a second description of the judgment: this
    /// syntax is the view paired with the kernel goal in `PropositionGoal`.
    fn try_structural_simp_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        match (surface_goal, goal) {
            (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                if let Some(enumerated) = self.try_finite_forall_enumeration(surface_goal)? {
                    return Ok(Some(enumerated));
                }
                match attempt::candidate_outcome(self.apply_step(SimpleProofStep::Intro))? {
                    Some(introduced) => introduced.try_simp_closure(),
                    None => Ok(None),
                }
            }
            (ClickProposition::Implies(surface_antecedent, _), Proposition::Implies(_, _)) => {
                let Some(mut introduced) =
                    attempt::candidate_outcome(self.apply_step(SimpleProofStep::Intro))?
                else {
                    return Ok(None);
                };
                // The introduced antecedent itself is the uniquely selected
                // contradiction candidate. This is a constant-size probe:
                // `Contradiction` checks that exact fact and its indexed
                // opposite, without scanning ambient path facts.
                if let Some(closed) = introduced
                    .try_introduced_antecedent_contradiction(surface_antecedent.as_ref())?
                {
                    return Ok(Some(closed));
                }
                let mut conjuncts = Vec::new();
                if matches!(surface_antecedent.as_ref(), ClickProposition::And(_, _)) {
                    collect_surface_conjunct_leaves(surface_antecedent, &mut conjuncts);
                }
                for conjunct in &conjuncts {
                    let Some(extracted) = attempt::candidate_outcome(
                        introduced.apply_step(SimpleProofStep::Extract(conjunct.clone())),
                    )?
                    else {
                        return Ok(None);
                    };
                    introduced = extracted;
                    if introduced.is_complete() {
                        return Ok(Some(introduced));
                    }
                }
                if !conjuncts.is_empty()
                    && let Some(surface_goal) = introduced.surface_goal()
                    && let Some(source) = old_reflexive_transport_source(surface_goal)
                {
                    match introduced.search_point_fact_transport(
                        &source,
                        surface_goal,
                        conjuncts.iter().cloned(),
                    ) {
                        Ok(transported) if transported.is_complete() => {
                            return Ok(Some(transported));
                        }
                        Ok(_) => {}
                        Err(_) => check_verification_deadline()?,
                    }
                }
                introduced.try_simp_closure()
            }
            (ClickProposition::And(surface_left, surface_right), Proposition::And(_, _)) => {
                let Some(left) =
                    attempt::candidate_outcome(self.begin_have(surface_left.as_ref().clone()))?
                else {
                    return Ok(None);
                };
                let Some(left) = left.try_simp_closure()? else {
                    return Ok(None);
                };
                let Some(proof) = attempt::candidate_outcome(left.join())? else {
                    return Ok(None);
                };
                let Some(right) =
                    attempt::candidate_outcome(proof.begin_have(surface_right.as_ref().clone()))?
                else {
                    return Ok(None);
                };
                let Some(right) = right.try_simp_closure()? else {
                    return Ok(None);
                };
                let Some(joined) = attempt::candidate_outcome(right.join())? else {
                    return Ok(None);
                };
                attempt::candidate_outcome(joined.apply_step(SimpleProofStep::Split))
            }
            // A predicate-call goal unfolds to its body, which the
            // structural arms and logical closers then work over. Repeat
            // unfolds are refused so recursive predicate bodies cannot loop
            // the search.
            (ClickProposition::PredicateCall { name, .. }, _)
                if !self.focused_goal_unfolds().contains(name) =>
            {
                match attempt::candidate_outcome(
                    self.apply_step(SimpleProofStep::UnfoldPredicate(name.clone())),
                )? {
                    Some(unfolded) => unfolded.try_simp_closure(),
                    None => Ok(None),
                }
            }
            (ClickProposition::Or(surface_left, surface_right), Proposition::Or(_, _)) => {
                for (surface, closer) in [
                    (surface_left.as_ref(), SimpleProofStep::Left),
                    (surface_right.as_ref(), SimpleProofStep::Right),
                ] {
                    let selected = (|| {
                        let Some(scope) =
                            attempt::candidate_outcome(self.begin_have(surface.clone()))?
                        else {
                            return Ok(None);
                        };
                        let Some(scope) = scope.try_simp_closure()? else {
                            return Ok(None);
                        };
                        let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                            return Ok(None);
                        };
                        attempt::candidate_outcome(joined.apply_step(closer.clone()))
                    })();
                    if let Some(selected) = selected? {
                        return Ok(Some(selected));
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    /// Proves the kernel's deterministic constant-bounded universal table as
    /// checked nested `have` scopes, then closes with the ordinary
    /// `Enumerate` rule. Candidate discovery is output-sensitive in the
    /// explicit instance table; each non-vacuous instance recursively uses
    /// the same retained Proof search and no ambient universal scan.
    fn try_finite_forall_enumeration(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Ok(None);
        };
        let mut binder_names = Vec::new();
        let mut surface_body = surface_goal;
        while let ClickProposition::ForAll { name, body, .. } = surface_body {
            binder_names.push(name.clone());
            surface_body = body;
        }
        if binder_names.is_empty() {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (values, instance) in instances {
            check_verification_deadline()?;
            if values.len() != binder_names.len() {
                return Ok(None);
            }
            if matches!(normalize_proposition(&instance), SimpProposition::True) {
                continue;
            }
            let Some(value_expressions) = values
                .iter()
                .map(|value| {
                    u32::try_from(*value)
                        .ok()
                        .map(|bits| ContractExpression::CFragment(CExpression::Value(int32(bits))))
                })
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            let substitutions = binder_names
                .iter()
                .cloned()
                .zip(value_expressions)
                .collect::<BTreeMap<_, _>>();
            let Ok(surface_instance) = substitute_click_proposition(surface_body, &substitutions)
            else {
                return Ok(None);
            };
            let Some(scope) = attempt::candidate_outcome(proof.begin_have(surface_instance))?
            else {
                return Ok(None);
            };
            let Some(scope) = scope.try_simp_closure()? else {
                return Ok(None);
            };
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.apply_step(SimpleProofStep::Enumerate))
    }

    /// Closes from the just-introduced antecedent and one exact indexed
    /// opposite. The antecedent fixes the kernel pair; Surface lookup visits
    /// only forms recorded for those two facts, never the ambient set.
    fn try_introduced_antecedent_contradiction(
        &self,
        surface_antecedent: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(introduced) = self.checked_facts().first() else {
            return Ok(None);
        };
        let opposite = match introduced {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        if !self.facts().contains(&opposite) {
            return Ok(None);
        }
        if let Some(closed) = attempt::candidate_outcome(
            self.apply_step(SimpleProofStep::Contradiction(surface_antecedent.clone())),
        )? {
            return Ok(Some(closed));
        }
        let surfaces = match self.context.as_ref() {
            ProofContext::Pure(context) => context
                .theorem_context
                .surface_requirements
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Point(context) => context
                .surface_propositions
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Execution(_) => self
                .outcome_point_view()
                .into_iter()
                .flat_map(|view| view.surface_propositions.surfaces(&opposite))
                .cloned()
                .collect::<Vec<_>>(),
        };
        for surface in surfaces {
            if let Some(closed) = attempt::candidate_outcome(
                self.apply_step(SimpleProofStep::Contradiction(surface)),
            )? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Retains the kernel decision and every exact replayable surface form
    /// among its context premises. A typed evidence translator selects and
    /// requires its own exact premises from this subset; unrelated transitive
    /// search context need not be Surface-synthesizable. This is a read-only smart
    /// query: only the later `apply_step` calls may advance the proof.
    fn selected_simp_derivation(
        &self,
        exclude_exact_goal: bool,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
    )> {
        let (surface_facts, theorem_application_closes_goal, premise_anchor) =
            match self.context.as_ref() {
                ProofContext::Pure(context) => {
                    (&context.theorem_context.surface_requirements, true, None)
                }
                ProofContext::Point(context) => (
                    context.surface_propositions,
                    true,
                    context.premise_anchor.as_ref(),
                ),
                // A judgment stated at a function outcome supplies the
                // outcome's recorded lowerings and statement-entry anchor.
                ProofContext::Execution(_) => {
                    let Some(point) = self.focused_outcome_point() else {
                        return None;
                    };
                    (
                        &point.surface_propositions,
                        // Entry-anchored premises can add a replay-equivalent
                        // outcome fact without discharging the exact goal
                        // form. Keep the ordinary trailing assumption so
                        // the checked successor decides whether it is needed.
                        false,
                        point.premise_anchor.as_ref(),
                    )
                }
            };
        let goal = self.goal()?.clone();
        let derivation = if exclude_exact_goal {
            self.facts()
                .assumptions()
                .derive_simp_proposition_without_exact_goal(&goal)?
        } else {
            let plan = plan_simp_certificate(&goal, self.facts().assumptions())?;
            let SimpEvidence::Derivation(derivation) = plan else {
                return None;
            };
            derivation
        };
        let context_premises = derivation.context_premises();
        let resolve_premise = |premise: &Proposition, anchor: Option<&ProgramPointRef>| {
            if let Some(surface) = self.replayable_surface_fact(surface_facts, anchor, premise) {
                return Some((premise.clone(), surface));
            }
            condition_polarity_forms(premise)
                .into_iter()
                .find_map(|form| {
                    let surface = self.replayable_surface_fact(surface_facts, anchor, &form);
                    surface.map(|surface| (form, surface))
                })
        };
        let mut premise_pairs = context_premises
            .iter()
            .filter_map(|premise| resolve_premise(premise, premise_anchor))
            .collect::<Vec<_>>();
        // A structured branch continuation can clear `last_step_entry`, or a
        // later common statement can move it past the point where the
        // selected premises were established. If the initially resolved
        // subset already carries one common explicit `at(...)` form,
        // retry this same finite premise list at that point. No ambient fact
        // or program-point scan participates.
        let anchors = premise_pairs
            .iter()
            .filter_map(|(_, surface)| surface_source_site(surface))
            .collect::<BTreeSet<_>>();
        if anchors.len() == 1 {
            let inferred = anchors.first().expect("one inferred anchor");
            let anchored_pairs = context_premises
                .iter()
                .filter_map(|premise| resolve_premise(premise, Some(inferred)))
                .collect::<Vec<_>>();
            if anchored_pairs.len() >= premise_pairs.len() {
                premise_pairs = anchored_pairs;
            }
        }
        Some((
            goal,
            derivation,
            premise_pairs,
            theorem_application_closes_goal,
        ))
    }

    /// Resolves one exact retained fact to a surface form that will lower
    /// back to that same kernel proposition when the selected simple step is
    /// replayed. Historical locals are anchored before ordinary forms are
    /// considered, so a same-written newer snapshot cannot be substituted.
    fn replayable_surface_fact(
        &self,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let matches_kernel = |candidate: &ClickProposition| {
            if self.focused_outcome_point().is_some()
                && surface_facts
                    .available_kernel_matching(candidate, |fact| self.facts().contains(fact))
                    .is_some_and(|lowered| {
                        lowered == kernel || condition_polarity_equivalent(lowered, kernel)
                    })
            {
                return Some(());
            }
            let lowered = self
                .lower_surface_proposition_direct(candidate, "typed simp premise form")
                .ok()?;
            (lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)).then_some(())
        };
        if let Some(surface) = surface_facts.surfaces(kernel).find(|surface| {
            (proposition_contains_at_expression(surface)
                || proposition_contains_old_expression(surface))
                && matches_kernel(surface).is_some()
        }) {
            return Some(surface.clone());
        }
        // Function requirements retain their original unanchored Surface
        // form while their kernel fact is entry-relative. Probe that one
        // canonical source site before the moving statement-entry anchor;
        // the direct lowering check below rejects non-entry facts, and the
        // lookup visits only forms indexed under this selected premise.
        let function_entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        if let Some(point) = self.focused_outcome_point()
            && let Some(surface) = point.requirement_surfaces.get(kernel)
        {
            let anchored = ClickProposition::At {
                selector: VisitSelector::ProgramPoint(function_entry.clone()),
                proposition: Box::new(surface.clone()),
            };
            if matches_kernel(&anchored).is_some() {
                return Some(anchored);
            }
            if let Ok(anchored) = surface_with_source_site(surface, &function_entry)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if self.focused_outcome_point().is_some() {
            if let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_with_source_site(surface, &function_entry).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            }) {
                return Some(anchored);
            }
            if let Some(view) = self.outcome_point_view()
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                )
                && let Ok(anchored) = surface_with_source_site(&surface, &function_entry)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(anchor) = premise_anchor
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_with_source_site(surface, anchor).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            })
        {
            return Some(anchored);
        }
        // A checked branch interface can export a kernel fact whose arm-local
        // Surface recording does not survive as a common map entry. The
        // statement-entry anchor still names the exact retained state. Rebuild
        // only this selected fact at that indexed state, anchor it, and require
        // the ordinary direct lowering to recover the same kernel premise.
        if let Some(anchor) = premise_anchor {
            let synthesis_context = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::Point(context) => Some((
                    context.parameters,
                    context.arguments,
                    context.program_point_states,
                )),
                ProofContext::Execution(_) => self
                    .outcome_point_view()
                    .map(|view| (view.parameters, view.arguments, view.program_point_states)),
            };
            if let Some((parameters, arguments, program_points)) = synthesis_context
                && let Some(state) = program_points.get(anchor)
                && let Some(surface) =
                    synthesize_surface_proposition(kernel, parameters, arguments, state)
                && let Ok(anchored) = surface_with_source_site(&surface, anchor)
                && matches_kernel(&anchored).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(surface) = surface_facts
            .surfaces(kernel)
            .find(|surface| matches_kernel(surface).is_some())
            .cloned()
        {
            return Some(surface);
        }
        // Quantified execution facts may be retained in the canonical memory
        // form used by the kernel while their recorded Surface form
        // lowers to a replay-equivalent snapshot term. Probe only the
        // persistent alpha/canonical-form bucket for this selected premise;
        // `InstantiateUsing` validates the same equivalence on replay.
        if matches!(kernel, Proposition::ForAll { .. }) {
            for candidate in self.facts().matching_quantified_replay_facts(kernel) {
                for surface in surface_facts.surfaces(&candidate) {
                    let lowered = self
                        .lower_surface_proposition_direct(
                            surface,
                            "typed quantified simp premise form",
                        )
                        .ok()?;
                    if quantified_replay_equivalent_available_fact(
                        kernel,
                        std::slice::from_ref(&lowered),
                    )
                    .is_some()
                    {
                        return Some(surface.clone());
                    }
                }
            }
        }
        // Branch-condition facts are checked execution outputs, but their
        // arm-local Surface map entry need not survive at the shared outcome.
        // Reconstruct only this derivation-selected premise at the current
        // semantic point and accept it only when ordinary lowering recovers
        // the exact kernel fact. This is constant work per typed proof edge,
        // not an ambient form search.
        let synthesis_context = match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::Point(context) => {
                Some((context.parameters, context.arguments, context.state))
            }
            ProofContext::Execution(_) => self
                .outcome_point_view()
                .map(|view| (view.parameters, view.arguments, view.state)),
        };
        let (parameters, arguments, state) = synthesis_context?;
        let surface = synthesize_surface_proposition(kernel, parameters, arguments, state)?;
        matches_kernel(&surface).map(|()| surface)
    }

    /// Tries equalities attached to terms occurring in the current goal.
    /// This complements the kernel derivation path for arithmetic goals whose
    /// normal form is exposed only after selected historical equalities are
    /// rewritten. Candidate lookup is goal-local and persistently indexed.
    /// Atomic goals may retain a same-width renaming, but each selected
    /// equality is used at most once; structural goals keep only a closing
    /// rewrite so their recursive connective proof remains visible.
    fn try_indexed_goal_equality_rewrite_closure(&self) -> Option<Self> {
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::Point(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => {
                let point = self.focused_outcome_point()?;
                (&point.surface_propositions, point.premise_anchor.as_ref())
            }
        };
        let mut proof = self.clone();
        let mut used = BTreeSet::new();
        loop {
            let goal = proof.goal()?.clone();
            let allows_chain = matches!(goal, Proposition::ConditionIs(_, _));
            let mut refinement = None;
            for equality in proof.facts().bitvector_equalities_mentioning(&goal) {
                if used.contains(&equality) {
                    continue;
                }
                let Some(surface) =
                    proof.replayable_surface_fact(surface_facts, premise_anchor, &equality)
                else {
                    continue;
                };
                // Rewriting is directional even when its admitted premise is
                // a symmetric equality. Keep the selected fact fixed, but
                // try both Surface orientations so the side occurring in the
                // focused goal can be replaced.
                let reverse = reverse_surface_equality(&surface);
                for oriented in std::iter::once(surface).chain(reverse) {
                    let Ok(rewritten) = proof.apply_step(SimpleProofStep::Rewrite(oriented)) else {
                        continue;
                    };
                    if let Some(closed) = rewritten
                        .try_direct_logical_closure()
                        .ok()
                        .flatten()
                        .or_else(|| rewritten.try_typed_atomic_simp_closure())
                    {
                        return Some(closed);
                    }
                    if allows_chain && refinement.is_none() && rewritten.goal() != Some(&goal) {
                        refinement = Some((equality.clone(), rewritten));
                    }
                }
            }
            let (equality, rewritten) = refinement?;
            used.insert(equality);
            proof = rewritten;
        }
    }

    /// Rewrites with only the explicitly selected equality premises, at most
    /// once each. Every candidate rewrite is checked transactionally, and
    /// the finite user-written premise list is the entire search space.
    fn try_selected_equality_rewrite_chain(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let mut proof = self.clone();
        let mut remaining = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true)
                )
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        while !remaining.is_empty() {
            let mut selected = None;
            for (index, surface) in remaining.iter().enumerate() {
                for oriented in
                    std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
                {
                    if let Ok(rewritten) = proof.apply_step(SimpleProofStep::Rewrite(oriented)) {
                        selected = Some((index, rewritten));
                        break;
                    }
                }
                if selected.is_some() {
                    break;
                }
            }
            let (index, rewritten) = selected?;
            remaining.remove(index);
            if let Some(closed) = rewritten
                .try_direct_logical_closure()
                .ok()
                .flatten()
                .or_else(|| rewritten.try_typed_atomic_simp_closure())
            {
                return Some(closed);
            }
            proof = rewritten;
        }
        None
    }

    /// Searches the structured predecessor proof already expressible through
    /// the checked API. The goal itself fixes the value and upper bound, so
    /// this visits only selected equalities connected to that value and one
    /// exact upper-bound premise; it never tries every partially synthesizable
    /// context fact as a candidate step.
    fn try_selected_predecessor_upper_bound(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if !matches!(self.context.as_ref(), ProofContext::Point(_)) {
            return None;
        }
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(predecessor, goal_upper),
            true,
        ) = goal
        else {
            return None;
        };
        let Bitvector32Term::Subtract(value, amount) = predecessor.as_ref() else {
            return None;
        };
        if amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        let upper_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(value.clone(), goal_upper.clone()),
            true,
        );
        let (_, upper_surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &upper_kernel)?;
        let (surface_value, surface_upper) = surface_nonstrict_parts(upper_surface)?;
        let nonnegative_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: surface_value.clone(),
        };
        for (kernel, surface) in premise_pairs {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                kernel
            else {
                continue;
            };
            let selected_constant = if left.as_ref() == value.as_ref() {
                right.as_ref()
            } else if right.as_ref() == value.as_ref() {
                left.as_ref()
            } else {
                continue;
            };
            let Bitvector32Term::Constant(bits) = selected_constant else {
                continue;
            };
            if (*bits as i32) < 0 {
                continue;
            }
            let mut orientations = vec![surface.clone()];
            if let Some(reverse) = reverse_surface_equality(surface)
                && reverse != *surface
            {
                orientations.push(reverse);
            }
            for equality in orientations {
                let scope = self.begin_have(nonnegative_surface.clone()).ok()?;
                let Ok(scope) = scope.apply_step(SimpleProofStep::Rewrite(equality)) else {
                    continue;
                };
                let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                    continue;
                };
                let joined = scope.join().ok()?;
                let theorem = SimpleProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "int32_nonnegative_predecessor_upper_bound".to_string(),
                        arguments: vec![surface_value.clone(), surface_upper.clone()],
                    },
                    premises: vec![nonnegative_surface.clone(), upper_surface.clone()],
                };
                let Ok(applied) = joined.apply_step(theorem) else {
                    continue;
                };
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                    return Some(closed);
                }
            }
        }
        None
    }

    /// Eliminates one disjunction selected by the kernel derivation and
    /// proves both arms on their branch-local `Proof`s. The disjunction is
    /// never reopened once either disjunct is already available, which makes
    /// recursive branch search descend through distinct case assumptions.
    fn try_selected_disjunction_cases(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        for (kernel, surface) in premise_pairs {
            let Proposition::Or(left, right) = kernel else {
                continue;
            };
            if self.facts().contains(left) || self.facts().contains(right) {
                continue;
            }
            let (surface_left, surface_right) = match surface {
                ClickProposition::Or(left, right) => {
                    (left.as_ref().clone(), right.as_ref().clone())
                }
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    let ClickProposition::Or(left, right) = proposition.as_ref() else {
                        continue;
                    };
                    (
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(left.as_ref().clone()),
                        },
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(right.as_ref().clone()),
                        },
                    )
                }
                _ => continue,
            };
            // The in-`Proof` split: both case goals coexist in one state,
            // each arm is proven by focusing its recorded id on this one
            // lineage, and the join partitions the retained steps by the
            // per-step goal attribution recorded when they were applied.
            let Ok((split_proof, split, ids)) = self.split_focused_cases(surface.clone()) else {
                continue;
            };
            let marker = split_proof.checkpoint();
            let branch_surfaces = [&surface_left, &surface_right];
            let mut proof = split_proof;
            let mut complete = true;
            for (id, assumed_surface) in ids.into_iter().zip(branch_surfaces) {
                let Ok(focused) = proof.focus(id) else {
                    complete = false;
                    break;
                };
                let selected = focused.try_simp_closure().ok().flatten().or_else(|| {
                    let rewritten = focused
                        .apply_step(SimpleProofStep::Rewrite(assumed_surface.clone()))
                        .ok()?;
                    rewritten
                        .try_direct_logical_closure()
                        .ok()
                        .flatten()
                        .or_else(|| rewritten.try_typed_atomic_simp_closure())
                });
                let Some(selected) = selected else {
                    complete = false;
                    break;
                };
                proof = selected;
            }
            if complete
                && let Ok(joined) = proof.join_focused_cases(&marker, split, ids, surface.clone())
            {
                return Some(joined);
            }
        }
        None
    }

    /// Applies a planner's flat explicit candidate directly to persistent
    /// `Proof` descendants. Planning may select surface operations, but only
    /// their ordinary checked implementations can advance the proof.
    ///
    /// Generated candidates historically retain a final `assumption()` even
    /// when the preceding operation already discharged the goal. Ignore only
    /// that final no-op; any other operation after closure rejects the
    /// candidate. No certificate is materialized or interpreted here.
    fn try_planned_explicit_steps(&self, tactics: &[ProofTactic]) -> Option<Self> {
        if tactics.is_empty() {
            return None;
        }
        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == tactics.len() && matches!(tactic, ProofTactic::Assumption) {
                    continue;
                }
                return None;
            }
            let step = explicit_linear_step(tactic)?;
            proof = proof.apply_step(step).ok()?;
        }
        proof.is_complete().then_some(proof)
    }

    /// Specializes one replayable universal premise selected by the atomic
    /// decision at the current goal. Planning only chooses the explicit
    /// quantified fact, argument, and guards; each selected operation advances
    /// this `Proof` directly.
    fn try_selected_forall_instantiation(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_instantiation(goal, premise_pairs)?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Tries only universal facts introduced by checked predicate unfolds when
    /// the atomic decision cannot name an instantiated premise. Candidate
    /// discovery is read-only; a specialization is retained only after the
    /// ordinary `InstantiateUsing` operation advances and closes this Proof.
    fn try_indexed_forall_instantiation(&self) -> Option<Self> {
        let goal = self.goal()?;
        let outcome_view = matches!(self.context.as_ref(), ProofContext::Execution(_))
            .then(|| self.outcome_point_view())
            .flatten();
        let bound_variable_names = match self.focused_goal() {
            Some(Goal::Proposition(goal)) => goal
                .surface_bindings
                .iter()
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Variable(variable),
                    ))) => Some((*variable, name.clone())),
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>(),
            _ => BTreeMap::new(),
        };
        let surface_form = |fact: &Proposition| {
            let recorded = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(fact)
                    .next()
                    .cloned(),
                ProofContext::Point(context) => {
                    context.surface_propositions.surfaces(fact).next().cloned()
                }
                ProofContext::Execution(_) => outcome_view
                    .as_ref()?
                    .surface_propositions
                    .surfaces(fact)
                    .next()
                    .cloned(),
            };
            let synthesized = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::Point(context) => {
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        context.parameters,
                        context.arguments,
                        context.state,
                        &bound_variable_names,
                    )
                }
                ProofContext::Execution(_) => {
                    let view = outcome_view.as_ref()?;
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        view.parameters,
                        view.arguments,
                        view.state,
                        &bound_variable_names,
                    )
                }
            };
            recorded.or(synthesized)
        };
        for quantified in self.facts().predicate_unfolded_universal_facts.iter() {
            // Reject shape-incompatible universals before Surface lookup or
            // synthesis. Candidate extraction is structural and bounded by
            // this one indexed fact and the focused goal; the expensive
            // form work is reserved for a specialization that can
            // actually mention the goal's concrete argument.
            let candidate_values =
                crate::kernel::forall_guided_instantiation_candidate_values(quantified, goal);
            let Proposition::ForAll { var, body, .. } = quantified else {
                unreachable!("the predicate-unfolded universal index contains only universals")
            };
            if candidate_values.is_empty() {
                continue;
            }
            let recorded_surfaces = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Point(context) => context
                    .surface_propositions
                    .surfaces(quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => outcome_view?
                    .surface_propositions
                    .surfaces(quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::Point(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let mut surfaces = Vec::new();
            for recorded in recorded_surfaces {
                let candidate = match recorded {
                    ClickProposition::PredicateCall {
                        ref name,
                        ref arguments,
                    } => predicate_environment.get(name).and_then(|definition| {
                        instantiate_click_predicate_definition(definition, arguments).ok()
                    }),
                    other => Some(other),
                };
                if let Some(candidate) = candidate
                    && !surfaces.contains(&candidate)
                {
                    surfaces.push(candidate);
                }
            }
            let synthesized = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::Point(context) => synthesize_surface_proposition(
                    quantified,
                    context.parameters,
                    context.arguments,
                    context.state,
                ),
                ProofContext::Execution(_) => {
                    let view = outcome_view?;
                    synthesize_surface_proposition(
                        quantified,
                        view.parameters,
                        view.arguments,
                        view.state,
                    )
                }
            };
            if let Some(synthesized) = synthesized
                && !surfaces.contains(&synthesized)
            {
                surfaces.push(synthesized);
            }
            // Unfolding retains the opaque predicate fact alongside its
            // checked body. Reconstruct that body's exact surface form
            // from only the active predicate indexes when generic synthesis
            // cannot express it (notably byte-indexed loads).
            if surfaces.is_empty() {
                let click_function_environment = match self.context.as_ref() {
                    ProofContext::Pure(context) => context.click_function_environment,
                    ProofContext::Point(context) => context.click_function_environment,
                    ProofContext::Execution(context) => context.click_function_environment,
                };
                for name in self.focused_goal_unfolds().iter() {
                    for opaque in self.facts().mentioning_predicate(name) {
                        let opaque_surfaces = match self.context.as_ref() {
                            ProofContext::Pure(context) => context
                                .theorem_context
                                .surface_requirements
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Point(context) => context
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Execution(_) => outcome_view?
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                        };
                        for opaque_surface in opaque_surfaces {
                            let ClickProposition::PredicateCall {
                                name: surface_name,
                                arguments,
                            } = opaque_surface
                            else {
                                continue;
                            };
                            let Some(definition) = predicate_environment.get(&surface_name) else {
                                continue;
                            };
                            let Ok(body_surface) =
                                instantiate_click_predicate_definition(definition, &arguments)
                            else {
                                continue;
                            };
                            if unfold_predicates_in_proposition(
                                predicate_environment,
                                click_function_environment,
                                std::slice::from_ref(name),
                                opaque,
                                self.facts().assumptions(),
                            )
                            .is_ok_and(|kernel| kernel == *quantified)
                                && !surfaces.contains(&body_surface)
                            {
                                surfaces.push(body_surface);
                            }
                        }
                    }
                }
            }
            for surface in surfaces {
                for value in candidate_values.iter().cloned() {
                    let argument = match &value {
                        Bitvector32Term::Constant(bits) => Some(ContractExpression::CFragment(
                            CExpression::Value(CValue::Int32(Bitvector32Term::Constant(*bits))),
                        )),
                        Bitvector32Term::Variable(variable) => {
                            let Some(Goal::Proposition(goal)) = self.focused_goal() else {
                                continue;
                            };
                            goal.surface_bindings.iter().find_map(|(name, binding)| {
                                matches!(
                                    binding,
                                    ContractExpression::CFragment(CExpression::Value(
                                        CValue::Int32(Bitvector32Term::Variable(bound))
                                    )) if bound == variable
                                )
                                .then(|| {
                                    ContractExpression::CFragment(CExpression::Variable(
                                        name.clone(),
                                    ))
                                })
                            })
                        }
                        _ => None,
                    };
                    let Some(argument) = argument else {
                        continue;
                    };
                    let instantiated =
                        substitute_int32_variable_in_proposition(body, *var, value.clone());
                    let mut guard_facts = Vec::new();
                    let mut current = &instantiated;
                    let mut guards_available = true;
                    while let Proposition::Implies(guard, consequent) = current {
                        let mut conjuncts = Vec::new();
                        atomic_conjuncts(guard, &mut conjuncts);
                        for conjunct in conjuncts {
                            if matches!(normalize_proposition(conjunct), SimpProposition::True) {
                                continue;
                            }
                            let exact = std::iter::once(conjunct.clone())
                                .chain(condition_polarity_forms(conjunct))
                                .find(|candidate| self.facts().contains(candidate));
                            let selected = exact.map(|fact| vec![fact]).or_else(|| {
                                self.facts()
                                    .assumptions()
                                    .derive_simp_atomic_proposition(conjunct)
                                    .map(|derivation| derivation.context_premises())
                            });
                            let Some(selected) = selected else {
                                guards_available = false;
                                break;
                            };
                            for actual in selected {
                                let Some(form) = surface_form(&actual) else {
                                    guards_available = false;
                                    break;
                                };
                                if !guard_facts
                                    .iter()
                                    .any(|(candidate, _)| candidate == &actual)
                                {
                                    guard_facts.push((actual, form));
                                }
                            }
                            if !guards_available {
                                break;
                            }
                        }
                        if !guards_available {
                            break;
                        }
                        current = consequent;
                    }
                    if !guards_available {
                        continue;
                    }
                    let instantiated_proof =
                        match self.apply_step(SimpleProofStep::InstantiateUsing {
                            quantified: surface.clone(),
                            argument: argument.clone(),
                            premises: guard_facts
                                .iter()
                                .map(|(_, surface)| surface.clone())
                                .collect(),
                        }) {
                            Ok(proof) => proof,
                            Err(_) => continue,
                        };
                    let conclusion = current.clone();
                    if &conclusion == goal || conclusion.clone() == goal.clone() {
                        if let Ok(closed) =
                            instantiated_proof.apply_step(SimpleProofStep::Assumption)
                        {
                            return Some(closed);
                        }
                        continue;
                    }

                    let transport_assumptions = self
                        .facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone());
                    let Some(transport_derivation) =
                        transport_assumptions.derive_simp_atomic_proposition(goal)
                    else {
                        continue;
                    };
                    let mut transport_surfaces = Vec::new();
                    let mut transport_written = true;
                    for premise in transport_derivation.context_premises() {
                        if premise == conclusion {
                            continue;
                        }
                        let Some(form) = surface_form(&premise) else {
                            transport_written = false;
                            break;
                        };
                        if !transport_surfaces.contains(&form) {
                            transport_surfaces.push(form);
                        }
                    }
                    if !transport_written {
                        continue;
                    }
                    let (selector, quantified_surface) = match &surface {
                        ClickProposition::At {
                            selector,
                            proposition,
                        } => (Some(selector.clone()), proposition.as_ref()),
                        other => (None, other),
                    };
                    let ClickProposition::ForAll {
                        name,
                        body: surface_body,
                        ..
                    } = quantified_surface
                    else {
                        continue;
                    };
                    let substitutions = std::iter::once((name.clone(), argument.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let Ok(mut source) = substitute_click_proposition(surface_body, &substitutions)
                    else {
                        continue;
                    };
                    while let ClickProposition::Implies(_, body) = source {
                        source = *body;
                    }
                    if let Some(selector) = selector {
                        source = ClickProposition::At {
                            selector,
                            proposition: Box::new(source),
                        };
                    }
                    transport_surfaces.insert(0, source.clone());
                    let target = self.surface_goal()?.clone();
                    match instantiated_proof.search_fact_transport_from_candidates(
                        &source,
                        &target,
                        transport_surfaces,
                        "indexed universal conclusion transport",
                    ) {
                        Ok(transported) if transported.is_complete() => return Some(transported),
                        Ok(_) | Err(_) => {}
                    }
                }
            }
        }
        None
    }

    /// Builds the binder-introduction chain from only the universal premises
    /// selected by the atomic decision. The planner never scans the ambient
    /// fact set; every resulting refinement applies directly to this `Proof`.
    fn try_selected_forall_goal(
        &self,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Retains the point-wise unchanged-load certificate for a guarded
    /// universal outcome. The kernel derivation has already selected the
    /// finite context premises relevant to this goal; after introducing the
    /// binder and guard, transport searches only those forms plus the
    /// freshly extracted guard leaves.
    fn try_selected_unchanged_load_forall_goal(
        &self,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if self.focused_outcome_point().is_none() {
            return None;
        }
        let mut cursor = surface_goal;
        let mut proof = self.clone();
        let mut introduced_forall = false;
        while let ClickProposition::ForAll { body, .. } = cursor {
            proof = proof.apply_step(SimpleProofStep::Intro).ok()?;
            cursor = body;
            introduced_forall = true;
        }
        if !introduced_forall {
            return None;
        }
        let ClickProposition::Implies(antecedent, _) = cursor else {
            return None;
        };
        proof = proof.apply_step(SimpleProofStep::Intro).ok()?;
        let mut guard_surfaces = Vec::new();
        collect_surface_conjunct_leaves(antecedent, &mut guard_surfaces);
        for guard in &guard_surfaces {
            proof = proof
                .apply_step(SimpleProofStep::Extract(guard.clone()))
                .ok()?;
        }
        let target = proof.surface_goal()?.clone();
        let source = old_reflexive_transport_source(&target)?;
        let source_pairs = proof
            .lower_surface_proposition(&source, "unchanged-load transport source")
            .ok()
            .and_then(|kernel| {
                proof
                    .facts()
                    .assumptions()
                    .derive_atomic_proposition(&kernel)
            })
            .map(|derivation| {
                let point = proof.focused_outcome_point()?;
                let pairs = derivation
                    .context_premises()
                    .into_iter()
                    .filter_map(|premise| {
                        proof
                            .replayable_surface_fact(
                                &point.surface_propositions,
                                point.premise_anchor.as_ref(),
                                &premise,
                            )
                            .map(|surface| (premise, surface))
                    })
                    .collect::<Vec<_>>();
                Some(pairs)
            })
            .flatten()
            .unwrap_or_default();
        let point = proof.focused_outcome_point()?;
        let anchor = point.premise_anchor.as_ref()?;
        let view = proof.outcome_point_view()?;
        let anchor_state = view.program_point_states.get(anchor)?;
        let mut anchored_candidates = Vec::new();
        for (kernel, _) in premise_pairs.iter().chain(&source_pairs) {
            let Some(surface) = synthesize_surface_proposition(
                kernel,
                view.parameters,
                view.arguments,
                anchor_state,
            ) else {
                continue;
            };
            let Ok(surface) = surface_with_source_site(&surface, anchor) else {
                continue;
            };
            let Some((left, right)) = surface_nonstrict_parts(&surface) else {
                continue;
            };
            let left_is_atomic_variable = match &left {
                ContractExpression::CFragment(CExpression::Variable(_)) => true,
                ContractExpression::At { expression, .. } => matches!(
                    expression.as_ref(),
                    ContractExpression::CFragment(CExpression::Variable(_))
                ),
                _ => false,
            };
            if left == right || !left_is_atomic_variable || anchored_candidates.contains(&surface) {
                continue;
            }
            let Ok(lowered) =
                proof.lower_surface_proposition(&surface, "unchanged-load transport premise")
            else {
                continue;
            };
            if lowered == *kernel || condition_polarity_equivalent(&lowered, kernel) {
                anchored_candidates.push(surface);
            }
        }
        // The source derivation must identify one exact non-strict bound at
        // the outcome anchor. Ambiguity is a prompt miss, never permission to
        // probe combinations of historical facts.
        let [anchored_candidate] = anchored_candidates.as_slice() else {
            return None;
        };
        let candidates = std::iter::once(anchored_candidate.clone()).chain(guard_surfaces);
        let transported = match proof.search_point_fact_transport(&source, &target, candidates) {
            Ok(transported) => transported,
            Err(error) => {
                let _ = error;
                return None;
            }
        };
        if transported.is_complete() {
            return Some(transported);
        }
        transported.try_direct_logical_closure().ok().flatten()
    }

    fn try_typed_atomic_simp_closure(&self) -> Option<Self> {
        let (goal, derivation, premise_pairs, point_application_closes_goal) =
            self.selected_simp_derivation(false)?;
        self.check_typed_atomic_simp_candidate(
            &goal,
            &derivation,
            &premise_pairs,
            point_application_closes_goal,
        )
    }

    /// Searches from exactly the Surface premises named by `simp() using`.
    /// This query cannot add facts or close the goal: it returns only the
    /// descendant obtained by checking the typed atomic decision through the
    /// ordinary Proof transitions.
    pub(super) fn try_restricted_simp_closure(
        &self,
        surfaces: &[ClickProposition],
    ) -> Option<Self> {
        // A named restricted premise may be a leaf of one exact available
        // conjunction (commonly after `unfold(predicate)`). Materialize that
        // leaf through the ordinary checked `extract` transition before
        // asking the restricted planner to use it. The returned descendant
        // therefore owns both the semantic fact and the Surface provenance;
        // expansion does not need to reconstruct and replay a certificate to
        // justify the premise later.
        let mut proof = self.clone();
        for surface in surfaces {
            let kernel = proof
                .lower_surface_proposition(surface, "restricted simp premise")
                .ok()?;
            if !proof.facts().contains_top_level(&kernel)
                && !normalizes_context_free(&kernel)
                && proof.facts().contains_proper_conjunct(&kernel)
            {
                proof = proof
                    .apply_step(SimpleProofStep::Extract(surface.clone()))
                    .ok()?;
                if proof.is_complete() {
                    return Some(proof);
                }
            }
        }
        let goal = proof.goal()?;
        let premise_pairs = surfaces
            .iter()
            .map(|surface| {
                let kernel = proof
                    .lower_surface_proposition(surface, "restricted simp premise")
                    .ok()?;
                // A listed premise that lowers to a context-free truth needs
                // no ambient fact authority. Retaining it lets the restricted
                // derivation erase reflexive field equalities after the
                // outcome state has evaluated their loads.
                (proof.facts().contains_top_level(&kernel) || normalizes_context_free(&kernel))
                    .then_some((kernel, surface.clone()))
            })
            .collect::<Option<Vec<_>>>()?;
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let plan = plan_simp_certificate(goal, &assumptions_from_propositions(&restricted))?;
        let SimpEvidence::Derivation(derivation) = &plan else {
            return None;
        };
        let theorem_application_closes_goal =
            !matches!(self.context.as_ref(), ProofContext::Execution(_));
        proof
            .check_typed_atomic_simp_candidate(
                goal,
                derivation,
                &premise_pairs,
                theorem_application_closes_goal,
            )
            .or_else(|| proof.try_selected_equality_rewrite_chain(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_order_transitivity(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_increment_order(&premise_pairs))
    }

    fn check_typed_atomic_simp_candidate(
        &self,
        goal: &Proposition,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
        point_application_closes_goal: bool,
    ) -> Option<Self> {
        let tactics = recorded_signed_order_pairs(derivation, &premise_pairs)
            .and_then(|ordered| {
                plan_recorded_signed_order_path_for_context(
                    goal,
                    &ordered,
                    point_application_closes_goal,
                )
            })
            .or_else(|| plan_recorded_bitvector_equality_path(goal, derivation, &premise_pairs))
            .or_else(|| {
                let recorded =
                    recorded_bitvector_equality_rewrite_path_pairs(derivation, &premise_pairs)?;
                plan_recorded_bitvector_equality_rewrite_paths(goal, derivation, &recorded)
            })
            .or_else(|| {
                plan_explicit_loadability_transport(goal, self.surface_goal()?, premise_pairs)
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_upper_bound_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_upper_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_constant_upper_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_constant_upper_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_strictly_increases_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_strictly_increases_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_one_plus_strictly_increases_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_one_plus_strictly_increases_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_below_max_is_defined_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_below_max_is_defined_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_one_plus_below_max_is_defined_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_one_plus_below_max_is_defined_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_nonnegative_add_within_max_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_nonnegative_add_within_max_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_nonnegative_subtract_within_value_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_nonnegative_subtract_within_value_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_lower_bound_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_lower_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_greater_equal_lower_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_greater_equal_lower_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_strict_greater_lower_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_strict_greater_lower_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_increment_strict_greater_from_strict_lower_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_increment_strict_greater_from_strict_lower_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_increment_preserves_order_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_increment_preserves_order_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_positive_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_positive_predecessor_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_positive_predecessor_strictly_decreases_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_positive_predecessor_strictly_decreases_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_nonnegative_predecessor_upper_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_equal_one_predecessor_is_zero_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_equal_one_predecessor_is_zero(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
                        derivation,
                        &premise_pairs,
                    )
                })?;
                plan_recorded_int32_equal_one_predecessor_for_context(
                    goal,
                    derivation,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_one_le_predecessor_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_one_le_predecessor_strictly_decreases_pairs(
                        derivation,
                        &premise_pairs,
                    )
                })?;
                plan_recorded_int32_one_le_predecessor_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_le_and_not_lt_implies_equality_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_ge_and_not_gt_implies_equality_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_ge_and_not_gt_implies_equality_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_positive_is_nonnegative_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_positive_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_strictly_positive_is_nonnegative_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_strictly_positive_is_nonnegative_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_successor_le_implies_lt_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_successor_le_implies_lt_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_constant_lower_bound_weakening_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_constant_lower_bound_weakening_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_int32_negated_strict_successor_bound_pairs(
                    derivation,
                    &premise_pairs,
                )?;
                plan_recorded_int32_negated_strict_successor_bound_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_le_and_neq_implies_strict_pairs(derivation, &premise_pairs)?;
                plan_recorded_int32_le_and_neq_implies_strict_for_context(
                    goal,
                    &recorded,
                    point_application_closes_goal,
                )
            })?;
        // The planner selects only Surface-expressible explicit operations.
        // Apply those through the same recursive Proof driver used by
        // authoritative source scripts; the plan is provenance input, not an
        // independently interpreted semantic certificate.
        let proof = self.try_planned_linear_script(&tactics).ok().flatten()?;
        proof.is_complete().then_some(proof)
    }

    /// Runs one branch arm of the linear script driver on the focused sibling
    /// goal. Both smart and explicit bodies apply their operations directly to
    /// this `Proof`; ordinary source interpretation does not first construct a
    /// certificate.
    fn try_focused_script_arm(
        &self,
        tactics: &[ProofTactic],
        authoritative: bool,
        generated: bool,
    ) -> Result<Option<Self>, ClickError> {
        if generated {
            self.try_planned_linear_script(tactics)
        } else if authoritative {
            self.try_authoritative_linear_script(tactics)
        } else {
            self.try_linear_script(tactics)
        }
    }

    /// Interprets one supported source script directly on this proof.
    ///
    /// Smart tactics search for checked descendants while explicit tactics
    /// apply their named operation. The returned proof already owns both the
    /// semantic result and its exact provenance; no certificate is constructed
    /// or replayed to establish acceptance.
    pub(super) fn try_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let contains_search = script_contains_linear_search(tactics);
        match self.try_linear_script_inner(tactics, false, false) {
            // Before this migration, an explicit-only script was checked by
            // the established source interpreter whenever the typed Proof
            // surface did not yet admit it. Preserve that transactional
            // fallback while successful explicit scripts take the direct
            // path. Smart-script failures retain their checked diagnostic.
            Err(_) if !contains_search && !crate::instrumentation::deadline_exceeded() => {
                #[cfg(test)]
                EXPLICIT_LINEAR_FALLBACKS.with(|fallbacks| fallbacks.set(fallbacks.get() + 1));
                Ok(None)
            }
            result => result,
        }
    }

    /// Checks source whose caller has already selected this Proof driver as
    /// the semantic authority. Explicit operation failures propagate instead
    /// of being converted into a compatibility miss; recursive scopes and
    /// branch arms inherit the same rule.
    pub(super) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_linear_script_inner(tactics, true, false)
    }

    /// Applies one planner-selected or expansion-generated Surface script to
    /// this Proof. Generated theorem plans may retain a final `assumption()`
    /// for outcome contexts where the theorem sometimes adds only an anchored
    /// equivalent fact. If an earlier checked operation closes that body
    /// exactly, only that final generated no-op is ignored. Ordinary explicit
    /// source scripts remain strict through `try_linear_script`.
    pub(super) fn try_planned_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_linear_script_inner(tactics, true, true)
    }

    fn try_linear_script_inner(
        &self,
        tactics: &[ProofTactic],
        authoritative: bool,
        generated: bool,
    ) -> Result<Option<Self>, ClickError> {
        if tactics.is_empty() {
            return Ok(None);
        }

        // Recognize the complete path before doing any search. `simp` closes
        // the remaining goal and is therefore meaningful only at the end.
        if !linear_script_is_supported(tactics) {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if generated
                    && index + 1 == tactics.len()
                    && matches!(tactic, ProofTactic::Assumption)
                {
                    continue;
                }
                // A final `simp` after an exact theorem conclusion is a
                // harmless search no-op and emits no redundant certificate
                // step, matching direct smart closure behavior.
                if matches!(tactic, ProofTactic::Simp) {
                    continue;
                }
                // Let the established explicit/source checker diagnose an
                // invalid suffix after closure. This path has produced no
                // externally visible mutation, and its source-level wording
                // remains part of the diagnostic contract.
                return Ok(None);
            }
            match tactic {
                ProofTactic::ApplyTheorem(application) => {
                    let Some(applied) = proof.try_theorem_application(application)? else {
                        return Ok(None);
                    };
                    proof = applied;
                }
                ProofTactic::Simp => {
                    let Some(closed) = proof.try_simp_closure()? else {
                        return Ok(None);
                    };
                    proof = closed;
                }
                ProofTactic::SimpUsing(simp) => {
                    let Some(closed) = proof.try_restricted_simp_closure(&simp.premises) else {
                        return Ok(None);
                    };
                    proof = closed;
                }
                ProofTactic::Have(have) => {
                    let scope = proof.begin_have(have.proposition.clone())?;
                    let selected = match &have.proof {
                        SourceProof::Default
                        | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
                            scope.try_simp_closure()?
                        }
                        SourceProof::Script(body) => {
                            if generated {
                                scope.try_planned_linear_script(body)?
                            } else if authoritative {
                                scope.try_authoritative_linear_script(body)?
                            } else {
                                scope.try_linear_script(body)?
                            }
                        }
                        SourceProof::Tactic(SmartTactic::Frame) => None,
                    };
                    let Some(selected) = selected else {
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let (split_proof, split, ids) =
                        proof.split_focused_if(proof_if.condition.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(then_done) = split_proof.focus(ids[0])?.try_focused_script_arm(
                        &proof_if.then_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(both_done) = then_done.focus(ids[1])?.try_focused_script_arm(
                        &proof_if.else_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = both_done.join_focused_if(
                        &marker,
                        split,
                        ids,
                        proof_if.condition.clone(),
                    )?;
                }
                ProofTactic::Cases(proof_cases) => {
                    let (split_proof, split, ids) =
                        proof.split_focused_cases(proof_cases.disjunction.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(left_done) = split_proof.focus(ids[0])?.try_focused_script_arm(
                        &proof_cases.left_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(both_done) = left_done.focus(ids[1])?.try_focused_script_arm(
                        &proof_cases.right_tactics,
                        authoritative,
                        generated,
                    )?
                    else {
                        return Ok(None);
                    };
                    proof = both_done.join_focused_cases(
                        &marker,
                        split,
                        ids,
                        proof_cases.disjunction.clone(),
                    )?;
                }
                tactic => {
                    let step = explicit_linear_step(tactic)
                        .expect("the linear script was recognized before execution");
                    proof = proof.apply_step(step)?;
                }
            }
        }

        Ok(proof.focused_discharged().then_some(proof))
    }

    /// Smart-only compatibility wrapper retained for focused regressions.
    #[cfg(test)]
    pub(super) fn try_linear_smart_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        if !script_contains_linear_search(tactics) {
            return Ok(None);
        }
        self.try_linear_script(tactics)
    }

    /// Whether this source proof is wholly represented by the recursive
    /// proposition driver. This is a syntax-only capability query.
    pub(super) fn supports_linear_source(proof: &SourceProof) -> bool {
        source_proof_is_supported(proof)
    }

    /// Tries a bounded linear statement candidate whose explicit dependencies
    /// are visible before executing the statement.
    ///
    /// This is deliberately narrower than general smart `step` planning. It
    /// requires a general statement's proof facts to consist exactly of
    /// expression-definedness evidence. A local assignment additionally
    /// selects current Surface facts indexed under the assigned name;
    /// unrelated facts remain shared and are never scanned. Selection performs
    /// indexed fact/surface lookups only; the C transition runs once, when the
    /// resulting `StepUsing` is submitted to `apply_step` and retained by the
    /// returned descendant.
    pub(super) fn try_indexed_statement_step(&self) -> Result<Option<Self>, ClickError> {
        self.try_indexed_statement_step_with_unrelated_context(false)
    }

    /// Selects one source smart statement step on this exact checked Proof.
    /// Preserve the established exact-context selection first; only when it
    /// cannot advance may unrelated retained effects or facts be shared by
    /// the broader checked selector. Both paths return only an accepted
    /// `StepUsing` descendant, never planning aftermath.
    pub(super) fn try_smart_step(&self) -> Result<Option<Self>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        // A raw-memory transition with no preceding call effect is fully
        // decided by the checked statement operation: the kernel retains
        // exactly the permissions and facts that survive it, so the returned
        // descendant is authoritative. A named entry resource may already
        // have been unfolded out of the current resource context, while a
        // call effect may carry a post-call surface fact needed by a later
        // statement. Both still require continuation-aware search (or an
        // explicit owned scope) before a standalone `step()` can select a
        // sufficient representation.
        if execution.replay.has_resource_surface_history
            || execution.state.resources().has_named_resources()
            || !execution.replay.effect_facts.is_empty()
        {
            return Ok(None);
        }
        if let Some(proof) = self.try_indexed_statement_step()? {
            return Ok(Some(proof));
        }
        self.try_indexed_execute_step()
    }

    /// The same bounded statement selection used by a scoped smart `execute`,
    /// where unrelated facts, resources, and effects remain shared across the
    /// checked transition instead of preventing a candidate. This is separate
    /// from standalone smart `step` so `execute` can traverse an open resource
    /// scope without changing `step`'s established explicit-certificate
    /// selection policy.
    pub(super) fn try_indexed_execute_step(&self) -> Result<Option<Self>, ClickError> {
        self.try_indexed_statement_step_with_unrelated_context(true)
    }

    fn try_indexed_statement_step_with_unrelated_context(
        &self,
        allow_unrelated_context: bool,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Err(self.step_error("execution-frontier proof lost its semantic state"));
        };
        if !allow_unrelated_context
            && (!execution.replay.effect_facts.is_empty()
                || !execution.state.resources().facts().is_empty()
                || self.facts().prioritized.is_some())
        {
            return Ok(None);
        }
        let (_, current_state, statement, _) = next_top_level_statement_from_execution_point(
            &execution.replay,
            &execution.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "smart step selection",
        )?;
        if matches!(statement, CStatement::If { .. } | CStatement::While { .. }) {
            return Ok(None);
        }
        let assigned_local = match &statement {
            CStatement::Assign { name, .. } => Some(name.as_str()),
            _ => None,
        };
        let mut required = statement_expression_definedness(&current_state, &statement)
            .into_iter()
            .filter(|fact| !PureFactContext::new().proves(fact))
            .collect::<Vec<_>>();
        required.sort();
        required.dedup();
        if !allow_unrelated_context
            && assigned_local.is_none()
            && self.facts().ordered.len() != required.len()
        {
            return Ok(None);
        }
        let mut selected = Vec::with_capacity(required.len());
        for fact in required {
            let Some(derivation) = self.facts().assumptions().derive_atomic_proposition(&fact)
            else {
                // Definedness may be discharged directly by the Proof-owned
                // resource context rather than by a pure proposition. Probe
                // the explicit empty candidate through the simple checker;
                // it either returns the checked descendant or leaves this
                // root untouched.
                if let Some(proof) = self.try_statement_step_using(Vec::new())? {
                    return Ok(Some(proof));
                }
                continue;
            };
            for premise in derivation.context_premises() {
                if !selected.contains(&premise) {
                    selected.push(premise);
                }
            }
        }
        if !allow_unrelated_context
            && assigned_local.is_none()
            && selected.len() != self.facts().ordered.len()
        {
            return Ok(None);
        }
        let mut indexed_dependencies = BTreeMap::new();
        if allow_unrelated_context {
            // A recent delta fact is a premise candidate only when the
            // focused goal actually owns it: a sibling split's delta spans
            // both arms, and the other arm's path fact may surface in this
            // arm's inherited replay record without being available here.
            for fact in self.state.added_facts.iter() {
                if self.facts().contains_top_level(fact)
                    && execution
                        .replay
                        .surface_propositions
                        .surfaces(fact)
                        .next()
                        .is_some()
                    && !selected.contains(fact)
                {
                    selected.push(fact.clone());
                }
            }
            if let Some(proof) = self.try_statement_step_with_selected_facts(
                execution,
                &selected,
                &indexed_dependencies,
            )? {
                return Ok(Some(proof));
            }
        }
        let mut dependency_names = BTreeSet::new();
        if allow_unrelated_context {
            collect_statement_variable_names(&statement, &mut dependency_names);
        } else if let Some(name) = assigned_local {
            dependency_names.insert(name.to_string());
        }
        for name in dependency_names {
            for fact in execution
                .replay
                .surface_propositions
                .current_c_variable_kernel_facts(&name)
            {
                if self.facts().contains_top_level(fact) {
                    indexed_dependencies
                        .entry(fact.clone())
                        .or_insert_with(|| name.clone());
                    if !selected.contains(fact) {
                        selected.push(fact.clone());
                        if allow_unrelated_context
                            && let Some(proof) = self.try_statement_step_with_selected_facts(
                                execution,
                                &selected,
                                &indexed_dependencies,
                            )?
                        {
                            return Ok(Some(proof));
                        }
                    }
                }
            }
        }
        if allow_unrelated_context {
            return Ok(None);
        }
        self.try_statement_step_with_selected_facts(execution, &selected, &indexed_dependencies)
    }

    fn try_statement_step_with_selected_facts(
        &self,
        execution: &ExecutionProofState,
        selected: &[Proposition],
        indexed_dependencies: &BTreeMap<Proposition, String>,
    ) -> Result<Option<Self>, ClickError> {
        let mut premises = Vec::with_capacity(selected.len());
        for fact in selected {
            let surface = indexed_dependencies
                .get(fact)
                .and_then(|name| {
                    execution
                        .replay
                        .surface_propositions
                        .current_c_variable_surface(&fact, name)
                })
                .or_else(|| execution.replay.surface_propositions.surfaces(&fact).next());
            let Some(surface) = surface.cloned() else {
                // A resource-local justification need not have a standalone
                // Surface proposition form. The empty simple candidate
                // remains the only sound fallback and is checked normally.
                return self.try_statement_step_using(Vec::new());
            };
            premises.push(surface);
        }
        self.try_statement_step_using(premises)
    }

    fn try_statement_step_using(
        &self,
        premises: Vec<ClickProposition>,
    ) -> Result<Option<Self>, ClickError> {
        match self.apply_step(SimpleProofStep::StepUsing(premises)) {
            Ok(proof) => Ok(Some(proof)),
            Err(_) => {
                check_verification_deadline()?;
                Ok(None)
            }
        }
    }

    /// Whether this execution proof has reached the function-exit frontier.
    ///
    /// This is a read-only smart-tactic query: it exposes no replay state and
    /// grants no authority to advance the proof.
    pub(super) fn is_at_function_exit(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.replay.is_at_function_exit())
    }

    /// Whether checked execution retained an infeasible sibling as an empty
    /// logical branch. Direct drivers use this Proof-owned structural fact to
    /// keep unsupported empty-leaf shapes on their compatibility routes.
    pub(super) fn has_empty_execution_branch_leaf(&self) -> bool {
        self.execution()
            .is_some_and(|execution| execution.has_empty_execution_branch_leaf)
    }

    /// Every open goal in this proof, in stable id order.
    pub(super) fn goals(&self) -> impl Iterator<Item = GoalId> + '_ {
        self.state.goals.open.keys().copied()
    }

    /// The open function-outcome goal derived for one checked path, if this
    /// proof owns it. Path indices are the checked execution's deterministic
    /// path order, recorded on each goal at derivation.
    pub(super) fn outcome_goal_for_path(&self, path_index: usize) -> Option<GoalId> {
        self.state
            .goals
            .open
            .iter()
            .find_map(|(id, goal)| match goal {
                Goal::FunctionOutcome(outcome) if outcome.path_index == path_index => Some(*id),
                _ => None,
            })
    }

    pub(super) fn focused_outcome_snapshot(&self) -> Result<CFunctionOutcome, ClickError> {
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("an outcome snapshot requires a focused outcome goal"));
        };
        Ok(CFunctionOutcome::Return {
            value: (*goal.point.result).clone(),
            state: (*goal.point.state).clone(),
        })
    }

    pub(super) fn checked_outcome_frame_authority(
        &self,
    ) -> Result<CheckedFrameAuthority, ClickError> {
        let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() else {
            return Err(self.step_error("frame authority requires a focused outcome goal"));
        };
        if !matches!(goal.selection, EffectGoalSelection::None) || goal.checked_effects.is_empty() {
            return Err(self.step_error("the focused outcome has no checked frame authority"));
        }
        Ok(CheckedFrameAuthority::new((*goal.checked_effects).clone()))
    }

    /// Updates the focused outcome goal's immutable result/state snapshot
    /// after a separately checked resource transition.
    pub(super) fn with_outcome_snapshot(
        &self,
        outcome: &CFunctionOutcome,
    ) -> Result<Self, ClickError> {
        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(self.step_error("an outcome snapshot requires a return outcome"));
        };
        let point = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => goal.point.as_ref(),
            Some(Goal::Proposition(goal)) => goal.outcome.as_deref().ok_or_else(|| {
                self.step_error("an outcome snapshot requires a result-aware proposition goal")
            })?,
            _ => {
                return Err(self.step_error("an outcome snapshot requires a focused outcome goal"));
            }
        };
        let mut point = point.clone();
        // Resource-producing post-execution tactics can replace the outcome
        // state after this goal was derived. Carry that persistent snapshot
        // root forward; otherwise later
        // checked point operations lower resource counts against the stale
        // pre-fold state. CState's components are shared immutable roots, so
        // this update is constant-size rather than a resource/history
        // materialization.
        point.result = Arc::new(value.clone());
        point.state = state.clone().into();
        let point = Arc::new(point);
        let mut state = (*self.state).clone();
        state.goals = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => {
                let mut updated = goal.clone();
                updated.point = point;
                state
                    .goals
                    .replace_at(self.focused, Goal::FunctionOutcome(updated))
            }
            Some(Goal::Proposition(goal)) => {
                let mut updated = goal.clone();
                updated.outcome = Some(point);
                state
                    .goals
                    .replace_at(self.focused, Goal::Proposition(updated))
            }
            _ => unreachable!("the outcome point was selected above"),
        };
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(state),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Installs an already checked post-execution fact context on the focused
    /// outcome goal while preserving retained Surface provenance for facts
    /// that survive the transition.
    pub(super) fn with_checked_outcome_facts(
        &self,
        facts: &[Proposition],
    ) -> Result<Self, ClickError> {
        let point = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => goal.point.as_ref(),
            Some(Goal::Proposition(goal)) => goal.outcome.as_deref().ok_or_else(|| {
                self.step_error("outcome facts require a result-aware proposition goal")
            })?,
            _ => return Err(self.step_error("outcome facts require a focused outcome goal")),
        };
        // Path preparation can unfold predicate requirements in place. Keep
        // the point view's requirement prefix aligned with the checked fact
        // context so indexed `choose` sources use that exact form.
        let requires = match self.context.as_ref() {
            ProofContext::Execution(context) => context.function_block.requires().len(),
            _ => 0,
        };
        let mut point = point.clone();
        point.requirement_facts = Arc::new(facts[..requires.min(facts.len())].to_vec());
        let point = Arc::new(point);
        let mut state = (*self.state).clone();
        state.goals = match self.focused_goal() {
            Some(Goal::FunctionOutcome(goal)) => {
                let mut updated = goal.clone();
                updated.point = point;
                state
                    .goals
                    .replace_at(self.focused, Goal::FunctionOutcome(updated))
            }
            Some(Goal::Proposition(goal)) => {
                let mut updated = goal.clone();
                updated.outcome = Some(point);
                state
                    .goals
                    .replace_at(self.focused, Goal::Proposition(updated))
            }
            _ => unreachable!("the outcome point was selected above"),
        };
        state.goals = state.goals.with_facts_at(
            self.focused,
            self.facts().resync_ordered_preserving_provenance(facts),
        );
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(state),
            node: self.node.clone(),
            focused: self.focused,
        })
    }

    /// Returns a handle addressing another open goal of the same state.
    ///
    /// Focus is a cursor: the returned handle shares this proof's semantic
    /// state and provenance, and checked operations through it advance
    /// exactly the addressed goal.
    /// The single open goal's id, when exactly one goal remains. Split
    /// regressions use it to name the pre-split obligation.
    #[cfg(test)]
    fn sole_goal_id(&self) -> Option<GoalId> {
        let mut ids = self.goals();
        let sole = ids.next()?;
        ids.next().is_none().then_some(sole)
    }

    pub(super) fn focus(&self, goal: GoalId) -> Result<Self, ClickError> {
        if self.state.goals.get(goal).is_none() {
            return Err(self.step_error(format!("goal {goal:?} is not open in this proof")));
        }
        let mut focused = self.clone();
        focused.focused = goal;
        Ok(focused)
    }

    /// Derives the typed function-outcome goal set from a function-exit
    /// frontier: the successor retires the focused frontier goal and opens
    /// one outcome goal per feasible checked returning path, in the checked
    /// execution's deterministic path order. Candidate paths whose exact
    /// facts contradict the enclosing proof facts contribute no goal.
    ///
    /// Each outcome goal owns its path's result value, post-outcome C state,
    /// and fact context (the frontier's facts extended by only that path's
    /// own facts), and borrows the frontier's snapshot by identity for
    /// lowering. A path proved non-returning contributes no goal. The
    /// returned handle addresses the first outcome goal; `focus` reaches its
    /// siblings. Result and effect continuations consume these goals
    /// directly rather than converting through the legacy replay adapter.
    pub(super) fn focus_function_outcomes(
        &self,
        requirement_facts: Arc<Vec<Proposition>>,
    ) -> Result<(Self, Vec<GoalId>), ClickError> {
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            return Err(self.step_error("outcome goals require an open execution frontier"));
        };
        let effect_selection = frontier.selection;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let checked = execution.replay.execution().ok_or_else(|| {
            self.step_error("outcome goals require execution to have reached function exit")
        })?;
        let frontier_snapshot = frontier.context.execution.clone();
        let frontier_unfolds = frontier.context.unfolded_predicates.clone();
        let frontier_surface = frontier_snapshot
            .as_ref()
            .map(|execution| execution.replay.surface_propositions.clone())
            .unwrap_or_default();
        let frontier_anchor = frontier_snapshot.as_ref().and_then(|execution| {
            execution
                .replay
                .proof_certificate_builder
                .last_step_entry
                .clone()
                .or_else(|| {
                    execution
                        .replay
                        .program_point_states
                        .keys()
                        .next_back()
                        .cloned()
                })
        });
        // Premises established across one statement use its entry snapshot
        // as their stable Surface Click spelling. A retained Proof may carry
        // the equivalent exit point as its most recent provenance marker;
        // prefer the matching recorded entry without changing the kernel
        // proposition or the outcome state being checked.
        let frontier_anchor = frontier_anchor.map(|anchor| {
            if anchor.kind != ProgramPointKind::Exit {
                return anchor;
            }
            let entry = ProgramPointRef {
                region: anchor.region.clone(),
                kind: ProgramPointKind::Entry,
            };
            frontier_snapshot
                .as_ref()
                .is_some_and(|execution| execution.replay.program_point_states.contains_key(&entry))
                .then_some(entry)
                .unwrap_or(anchor)
        });
        let requirement_surfaces = match self.context.as_ref() {
            ProofContext::Execution(context) => requirement_facts
                .iter()
                .zip(context.function_block.requires())
                .filter_map(|(fact, requirement)| {
                    requirement
                        .proposition()
                        .cloned()
                        .map(|surface| (fact.clone(), surface))
                })
                .fold(PersistentMap::default(), |index, (fact, surface)| {
                    index.with_inserted(fact, surface)
                }),
            _ => PersistentMap::default(),
        };
        let requirement_surfaces = Arc::new(requirement_surfaces);
        let mut goals = self.state.goals.discharge_at(self.focused);
        let mut outcome_ids = Vec::new();
        for (path_index, path) in checked.paths().iter().enumerate() {
            // One checked statement may produce several candidate outcomes.
            // The enclosing Proof facts select the feasible successors; an
            // exact contradictory path fact cannot become a typed outcome
            // goal merely because the legacy execution container retained
            // every candidate. Preserve the original path index so later
            // finalization addresses the checked candidate without rebuilding
            // or renumbering the path set.
            if path
                .facts()
                .iter()
                .any(|fact| self.facts().directly_conflicts_with(fact.proposition()))
            {
                continue;
            }
            let (result, state) = match path.outcome() {
                CFunctionOutcome::Return { value, state } => (value.clone(), state.clone()),
                // A path proved non-returning owes no outcome judgment.
                CFunctionOutcome::VerificationDiverges => continue,
                CFunctionOutcome::UndefinedBehavior(_) | CFunctionOutcome::RuntimeError(_) => {
                    return Err(self.step_error(format!(
                        "outcome goals require a verifying execution, but path {path_index} failed"
                    )));
                }
            };
            // The goal owns the path-local pure facts. Effect-region facts
            // stay in the execution snapshot and are consumed only by the
            // checked point operations that explicitly cross effects.
            let mut facts = self.facts().clone();
            for fact in path.facts() {
                facts = facts.with_fact(fact.proposition().clone());
            }
            let execution_facts = path.execution_facts();
            let id = GoalId(goals.next_id);
            goals = ProofGoals {
                open: goals.open.with_inserted(
                    id,
                    Goal::FunctionOutcome(OutcomeGoal {
                        path_index,
                        selection: effect_selection,
                        checked_effects: Arc::new(Vec::new()),
                        point: Arc::new(OutcomePointData {
                            result: Arc::new(result),
                            state: state.into(),
                            surface_propositions: frontier_surface.clone(),
                            effect_facts: Arc::new(execution_facts),
                            execution_pure_facts: Arc::new(path.facts().to_vec()),
                            premise_anchor: frontier_anchor.clone(),
                            requirement_facts: requirement_facts.clone(),
                            requirement_surfaces: requirement_surfaces.clone(),
                            branch_decisions: execution
                                .outcome_branch_decisions
                                .get(path_index)
                                .cloned()
                                .unwrap_or_else(|| execution.branch_decisions.clone()),
                        }),
                        context: GoalContext {
                            facts,
                            unfolded_predicates: frontier_unfolds.clone(),
                            execution: frontier_snapshot.clone(),
                        },
                    }),
                ),
                next_id: goals.next_id + 1,
            };
            outcome_ids.push(id);
        }
        if outcome_ids.is_empty() {
            return Err(self.step_error("outcome goals require at least one returning path"));
        }
        let successor = Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),

                goals,
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            // A structural marker records the derivation; the certificate
            // step vocabulary for consuming outcome goals arrives with the
            // drain migration.
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused: self.focused,
                depth: self.node.depth,
            }),
            focused: outcome_ids[0],
        };
        Ok((successor, outcome_ids))
    }

    /// Whether the checked execution frontier is a structural C `if`.
    ///
    /// Smart `execute` uses this read-only query to distinguish a structural
    /// frontier from an ordinary statement whose indexed candidate simply did
    /// not apply. It grants no branch authority and performs no transition.
    pub(super) fn is_at_execution_branch(&self) -> Result<bool, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))?;
        if execution.replay.is_at_function_exit() {
            return Ok(false);
        }
        if execution.state.memory().has_pending_heap_allocation() {
            // A pending malloc result is an independent execution split. The
            // current branch container owns one C-condition split, not the
            // Cartesian product of both; compatibility execution retains
            // that frontier from the unchanged Proof root.
            return Ok(false);
        }
        let statement_index = execution.replay.frontier.next_statement_index;
        let source_region = execution
            .replay
            .source_layout
            .statement(statement_index)
            .ok_or_else(|| {
                self.step_error(format!(
                    "could not resolve source statement({statement_index})"
                ))
            })?;
        Ok(matches!(source_region.kind, SourceStatementKind::If { .. }))
    }

    /// Resolves a Surface Click statement region against this proof's source
    /// layout without exposing the mutable frontier or replay metadata.
    fn resolve_statement_target(&self, region: &CodeRegionRef) -> Result<usize, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`execute_until` requires an execution proof"));
        };
        let CodeRegion::Statement(statement_index) = resolve_code_region_ref(
            context.function_block,
            region,
            context.claim_label,
            context.tactic_index,
        )?
        else {
            return Err(self.step_error("`execute_until` expects a statement region"));
        };
        Ok(statement_index)
    }

    /// Returns the current source-statement frontier for a checked execution
    /// proof, or `None` after function exit.
    fn current_statement_index(&self) -> Result<Option<usize>, ClickError> {
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution proof lost its semantic frontier"))?;
        Ok((!execution.replay.is_at_function_exit())
            .then_some(execution.replay.frontier.next_statement_index))
    }

    /// Searches a straight-line prefix up to one named statement by applying
    /// every selected `StepUsing` to the current checked descendant. The
    /// returned fact list is only the prefix's output delta; scope adapters
    /// use it to retain facts introduced inside their owned representation.
    fn try_linear_execute_until_descendant(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        let target = self.resolve_statement_target(region)?;
        let Some(current) = self.current_statement_index()? else {
            return Err(self.step_error(format!(
                "`execute_until(statement({target}))` cannot run after execution already reached function exit"
            )));
        };
        if target < current {
            return Err(self.step_error(format!(
                "`execute_until(statement({target}))` cannot move backward from statement({current})"
            )));
        }

        let mut proof = self.clone();
        let mut introduced_facts = Vec::new();
        let mut advanced = false;
        loop {
            match proof.current_statement_index()? {
                Some(current) if current == target => break,
                Some(current) if current < target => {}
                Some(_) | None => return Ok(None),
            }
            // The first statement must be independent of unrelated facts in
            // the inherited root context. After it advances, the descendant
            // owns an explicit output-sized `added_facts` delta; the checked
            // execute selector carries only that delta through later steps.
            let next = if advanced {
                proof.try_indexed_execute_step()?
            } else {
                proof.try_indexed_statement_step()?
            };
            let Some(next) = next else {
                return Ok(None);
            };
            for fact in next.added_facts() {
                if !introduced_facts.contains(fact) {
                    introduced_facts.push(fact.clone());
                }
            }
            proof = next;
            advanced = true;
        }
        Ok(advanced.then_some((proof, introduced_facts)))
    }

    /// Runs the narrow checked `execute_until` search on this Proof and
    /// returns only the already-accepted descendant.
    pub(super) fn try_linear_execute_until(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<Self>, ClickError> {
        Ok(self
            .try_linear_execute_until_descendant(region)?
            .map(|(proof, _)| proof))
    }

    /// Runs the narrow linear `execute` search over checked descendants.
    /// Straight-line statements and audited terminal C branches advance only
    /// through their Proof operations; a partial path is discarded unless it
    /// reaches function exit.
    fn try_linear_execute_descendant(
        &self,
    ) -> Result<Option<(Self, Vec<Proposition>)>, ClickError> {
        let mut proof = self.clone();
        let mut introduced_facts = Vec::new();
        let mut advanced = false;
        while !proof.is_at_function_exit() {
            let next = if let Some(next) = proof.try_indexed_execute_step()? {
                next
            } else {
                if !proof.is_at_execution_branch()? {
                    return Ok(None);
                }
                let Some(next) = proof.try_focused_execute_to_exit()? else {
                    return Ok(None);
                };
                next
            };
            for fact in next.added_facts() {
                if !introduced_facts.contains(fact) {
                    introduced_facts.push(fact.clone());
                }
            }
            proof = next;
            advanced = true;
        }
        if !advanced {
            return Ok(None);
        }
        Ok(Some((proof, introduced_facts)))
    }

    /// Returns the already-checked function-exit descendant selected by the
    /// narrow linear `execute` search.
    pub(super) fn try_linear_execute(&self) -> Result<Option<Self>, ClickError> {
        Ok(self
            .try_linear_execute_descendant()?
            .map(|(proof, _)| proof))
    }

    /// Runs top-level `execute` from an exact execution root. With no ambient
    /// proof facts, resources, or effect facts to transport, the existing
    /// checked branch container may own structural C forks as well as linear
    /// statements without guessing what a later continuation will need.
    pub(super) fn try_exact_execute_to_exit(&self) -> Result<Option<Self>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        if !self.facts().ordered.is_empty()
            || self.facts().prioritized.is_some()
            || !execution.state.resources().facts().is_empty()
            || !execution.replay.effect_facts.is_empty()
            || !execution.replay.case_assumptions.is_empty()
        {
            return Ok(None);
        }
        self.try_linear_execute()
    }

    /// Searches explicit premise forms for one point fact transport.
    ///
    /// Every candidate is checked by applying the corresponding simple step
    /// to this immutable root. Failed descendants are discarded; the
    /// returned `Proof` is the already-checked, deletion-minimized success,
    /// so callers never reconstruct or replay the selected certificate.
    pub(super) fn search_point_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
    ) -> Result<Self, ClickError> {
        let result_aware = matches!(self.context.as_ref(), ProofContext::Point(_))
            || self.focused_outcome_point().is_some();
        if !result_aware {
            return Err(self.step_error(
                "fact-transport search requires a point proof or a focused outcome goal",
            ));
        }
        self.search_fact_transport_from_candidates(
            source,
            target,
            candidates,
            "post-execution fact transport",
        )
    }

    /// Tries the bounded source-local form of mid-execution fact transport on
    /// this immutable execution Proof. The smart operation checks the empty
    /// candidate and the source's own explicit form; it never scans the
    /// ambient fact set. Richer premise discovery remains on the legacy path
    /// until it has a relevance index rather than an environment-wide scan.
    pub(super) fn try_execution_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(_) = self.context.as_ref() else {
            return Err(
                self.step_error("execution fact-transport search requires an execution proof")
            );
        };
        let execution = self.execution().ok_or_else(|| {
            self.step_error("execution fact-transport search lost its semantic frontier")
        })?;
        if execution.replay.is_at_function_entry() {
            return Err(self.step_error(
                "`transport` requires a current statement frontier after at least one execution step",
            ));
        }
        if execution.replay.is_at_function_exit() {
            return Ok(None);
        }
        match self.search_fact_transport_from_candidates(
            source,
            target,
            std::iter::once(source.clone()),
            "execution-frontier fact transport",
        ) {
            Ok(proof) => Ok(Some(proof)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    fn search_fact_transport_from_candidates(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        candidates: impl IntoIterator<Item = ClickProposition>,
        description: &str,
    ) -> Result<Self, ClickError> {
        let apply = |premises: Vec<ClickProposition>| {
            self.apply_step(SimpleProofStep::TransportUsing {
                source: source.clone(),
                target: target.clone(),
                premises,
            })
        };
        let mut selected = Vec::new();
        let mut last_error = None;
        let mut selected_proof = match apply(Vec::new()) {
            Ok(proof) => Some(proof),
            Err(error) => {
                last_error = Some(error);
                check_verification_deadline()?;
                None
            }
        };
        if selected_proof.is_none() {
            for candidate in candidates {
                check_verification_deadline()?;
                if selected.contains(&candidate) {
                    continue;
                }
                selected.push(candidate);
                match apply(selected.clone()) {
                    Ok(proof) => {
                        selected_proof = Some(proof);
                        break;
                    }
                    Err(error) => {
                        last_error = Some(error);
                        check_verification_deadline()?;
                    }
                }
            }
        }
        let Some(mut selected_proof) = selected_proof else {
            return Err(self.step_error(format!(
                "{description} has no explicit surface-premise certificate: {}",
                last_error
                    .as_ref()
                    .map(|error| error.message())
                    .unwrap_or("no candidate was checked")
            )));
        };
        let mut index = 0;
        while index < selected.len() {
            check_verification_deadline()?;
            let mut reduced = selected.clone();
            reduced.remove(index);
            match apply(reduced.clone()) {
                Ok(proof) => {
                    selected = reduced;
                    selected_proof = proof;
                }
                Err(_) => {
                    check_verification_deadline()?;
                    index += 1;
                }
            }
        }
        Ok(selected_proof)
    }

    /// Untrusted smart-tactic query for one explicit theorem-application
    /// candidate on a point proof.
    ///
    /// Requirement selection probes the current persistent fact indexes. It
    /// returns only a `SimpleProofStep`; theorem conclusions and provenance
    /// are created later, if and only if the caller submits that step to
    /// `apply_step` on this same proof.
    pub(super) fn select_point_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<SimpleProofStep, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("point theorem-application search requires a point proof"));
        };
        self.select_theorem_application_step_at_point(
            application,
            context.parameters,
            context.arguments,
            context.pre_state,
            context.state,
            context.result,
            context.program_point_states,
            context.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.theorem_environment,
        )
    }

    /// Untrusted smart-tactic query for one explicit theorem step at the
    /// current execution frontier. The query can inspect the immutable proof
    /// and return syntax, but only `apply_step` can add the conclusion or
    /// advance provenance.
    pub(super) fn select_execution_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<SimpleProofStep, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "execution theorem-application search requires an execution-frontier proof",
            ));
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let pre_state = execution.replay.old_reference_state(&execution.state);
        self.select_theorem_application_step_at_point(
            application,
            context.parsed_function.parameters(),
            context.arguments,
            pre_state,
            &execution.state,
            None,
            &execution.replay.program_point_states,
            &execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.theorem_environment,
        )
    }

    /// Tries one bare theorem application against this immutable Proof.
    ///
    /// Selection is context-specific, but every context returns the same
    /// explicit `ApplyTheoremUsing` candidate and submits it to `apply_step`
    /// on this exact root. A selection miss is transactional; once selection
    /// succeeds, rejection by the checker is a loud implementation error
    /// rather than permission to retry through a second semantic path.
    pub(super) fn try_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<Self>, ClickError> {
        let selected = self.select_theorem_application_step(application);
        let step = match selected {
            Ok(Some(step)) => step,
            Ok(None) => return Ok(None),
            Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
            Err(_) => return Ok(None),
        };
        self.apply_selected_theorem_application(step).map(Some)
    }

    /// Applies one bare theorem application without treating an unavailable
    /// candidate as a smart-search miss. Source adapters that have already
    /// committed to `apply(...)` use this strict form and retain the original
    /// selector diagnostic, while still sharing the sole checked transition.
    pub(super) fn apply_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Self, ClickError> {
        let Some(step) = self.select_theorem_application_step(application)? else {
            return Err(self.step_error(
                "theorem application requires a result-sensitive point proof after function exit",
            ));
        };
        self.apply_selected_theorem_application(step)
    }

    fn select_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<SimpleProofStep>, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.select_pure_theorem_application_step(application),
            ProofContext::Point(_) => self.select_point_theorem_application_step(application),
            // A focused function-outcome goal is one result-sensitive point
            // context: selection reads the goal-aware view directly.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view_with_effects(OutcomeEffectContext::Replay)
                    .expect("a focused outcome judgment resolves its point view");
                self.select_theorem_application_step_at_point(
                    application,
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.program_point_states,
                    view.surface_propositions,
                    view.predicate_environment,
                    view.click_function_environment,
                    view.theorem_environment,
                )
            }
            ProofContext::Execution(_) if !self.is_at_function_exit() => {
                self.select_execution_theorem_application_step(application)
            }
            // A function-exit execution Proof not focused on one outcome
            // still owns several result-sensitive point contexts; ordered
            // finalization keeps that seam until its paths derive goals.
            ProofContext::Execution(_) => return Ok(None),
        }
        .map(Some)
    }

    fn apply_selected_theorem_application(
        &self,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step(step).map_err(|error| {
            self.step_error(format!(
                "theorem search selected a simple candidate that Proof rejected: {}",
                error.message()
            ))
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn select_theorem_application_step_at_point(
        &self,
        application: &TheoremApplication,
        parameters: &[syntax::C0Parameter],
        arguments: &[CExpression],
        pre_state: &CState,
        state: &CState,
        result: Option<&CValue>,
        program_point_states: &ProgramPointStates,
        surface_propositions: &SurfacePropositionMap,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
        theorem_environment: &TheoremEnvironment,
    ) -> Result<SimpleProofStep, ClickError> {
        let values = parameter_values(parameters, arguments).map_err(|error| {
            self.step_error(format!(
                "could not bind theorem arguments: {}",
                error.message
            ))
        })?;
        let array_refs = array_refs_for_parameters(parameters, &values, state.memory());
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, state);
        let application_context = TheoremApplicationContext {
            values: &values,
            array_refs: &array_refs,
            pre_state,
            post_state: state,
            result,
            program_point_states,
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let mut lowering_assumptions = self.facts().assumptions().clone();
        for fact in state
            .resources()
            .observable_facts_assuming_valid(self.facts().assumptions())
        {
            lowering_assumptions = lowering_assumptions.assume_proposition(fact);
        }
        let requirements = lower_theorem_application_requirements_with_assumptions(
            theorem_environment,
            application,
            &application_context,
            &lowering_assumptions,
            predicate_environment,
            click_function_environment,
            &unfolded_predicates,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower theorem requirements: {message}"))
        })?;

        let mut premises = Vec::new();
        for requirement in requirements {
            if matches!(normalize_proposition(&requirement), SimpProposition::True) {
                continue;
            }
            let matched = self                .facts()                .matching_replay_fact_across_effects(&requirement, &[])
                .ok_or_else(|| {
                    self.step_error(format!(
                        "theorem application `{}` requires an unavailable exact premise: {requirement:?}",
                        application.name
                    ))
                })?;

            // Reuse the established snapshot-surface search for execution
            // proofs, with availability answered by persistent indexes. The
            // canonical fact above comes from the requirement's shape bucket,
            // so sibling snapshot terms remain visible without rebuilding
            // the complete ambient fact vector. The returned form still
            // has to survive `apply_step` below.
            let mut snapshot_surface_error = None;
            if let ProofContext::Execution(_) = self.context.as_ref() {
                let execution = self
                    .execution()
                    .expect("execution proof owns semantic state");
                match checked_surface_comparison_fact_at_point_with_indexed_facts(
                    &execution.replay,
                    &matched,
                    SurfaceFactMatch::CanonicalExact,
                    &self.facts(),
                    &lowering_assumptions,
                    parameters,
                    arguments,
                    state,
                    predicate_environment,
                    click_function_environment,
                ) {
                    Ok(surface) => {
                        if !premises.contains(&surface) {
                            premises.push(surface);
                        }
                        continue;
                    }
                    Err(error) => snapshot_surface_error = Some(error),
                }
            }

            let mut candidates = surface_propositions
                .surfaces(&matched)
                .chain(surface_propositions.surfaces(&requirement))
                .cloned()
                .collect::<Vec<_>>();
            if let Some(candidate) =
                synthesize_surface_proposition(&matched, parameters, arguments, state)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            if let Some(candidate) =
                synthesize_surface_proposition(&requirement, parameters, arguments, state)
                && !candidates.contains(&candidate)
            {
                candidates.push(candidate);
            }
            if candidates.is_empty() {
                return Err(self.step_error(format!(
                    "theorem application `{}` has no checked surface form for exact premise `{requirement:?}`",
                    application.name
                )));
            }
            let surface = candidates
                .into_iter()
                // SurfacePropositionMap treats the most recently recorded
                // form as canonical. Prefer it here too; earlier entries
                // can be mechanically valid but over-anchor constants as
                // `at(point, constant)` and produce needlessly unstable
                // certificates.
                .rev()
                .find(|candidate| {
                    let matches_requirement = |lowered: &Proposition| {
                        (lowered.clone()
                            == requirement.clone()
                            || condition_polarity_equivalent(lowered, &requirement))
                            && self                                .facts()                                .replay_available_across_effects(lowered, &[])
                    };
                    let direct = lower_point_proposition_with_assumptions(
                        candidate,
                        &lowering_assumptions,
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        result,
                        program_point_states,
                        predicate_environment,
                        click_function_environment,
                    );
                    direct.as_ref().is_ok_and(matches_requirement)
                })
                .ok_or_else(|| {
                    self.step_error(format!(
                        "theorem application `{}` has no checked surface form for exact premise `{requirement:?}`{}",
                        application.name,
                        snapshot_surface_error
                            .as_ref()
                            .map(|error| format!(": {}", error.message()))
                            .unwrap_or_default(),
                    ))
                })?;
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }

        Ok(SimpleProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises,
        })
    }

    /// Untrusted pure smart-tactic query for one explicit theorem step.
    /// This instantiates the applied theorem's own requirement forms and
    /// probes their lowered forms through the current persistent fact index;
    /// it cannot advance the proof or add the theorem's conclusion.
    pub(super) fn select_pure_theorem_application_step(
        &self,
        application: &TheoremApplication,
    ) -> Result<SimpleProofStep, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(
                self.step_error("pure theorem-application search requires a proposition goal")
            );
        };
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let program_point_states = ProgramPointStates::new();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            pre_state: &state,
            post_state: &state,
            result: None,
            program_point_states: &program_point_states,
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let requirements = lower_theorem_application_requirements_with_assumptions(
            context.theorem_environment,
            application,
            &application_context,
            self.facts().assumptions(),
            context.predicate_environment,
            context.click_function_environment,
            &unfolded_predicates,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower theorem requirements: {message}"))
        })?;
        let theorem = context
            .theorem_environment
            .get(&application.name)
            .ok_or_else(|| self.step_error(format!("unknown theorem `{}`", application.name)))?;
        let substitutions = theorem
            .parameters()
            .iter()
            .map(FunctionParameter::name)
            .map(str::to_string)
            .zip(application.arguments.iter().cloned())
            .collect::<BTreeMap<_, _>>();

        let mut premises = Vec::new();
        for (requirement, source_requirement) in requirements.into_iter().zip(theorem.requires()) {
            if normalizes_context_free(&requirement) {
                continue;
            }
            let source_surface = source_requirement.proposition().ok_or_else(|| {
                self.step_error(format!(
                    "theorem application `{}` has a non-proposition requirement",
                    application.name
                ))
            })?;
            let surface = substitute_click_proposition(source_surface, &substitutions)
                .map_err(|message| self.step_error(message))?;
            let lowered = self.lower_surface_proposition(&surface, "selected theorem premise")?;
            if lowered.clone() != requirement.clone() || !self.facts().contains(&lowered) {
                return Err(self.step_error(format!(
                    "required exact fact for theorem `{}` is unavailable: {requirement:?}",
                    application.name
                )));
            }
            if !premises.contains(&surface) {
                premises.push(surface);
            }
        }
        Ok(SimpleProofStep::ApplyTheoremUsing {
            application: application.clone(),
            premises,
        })
    }

    fn apply_theorem_using(
        &self,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                self.apply_pure_theorem_using(context, application, surface_premises)
            }
            ProofContext::Point(context) => self.apply_point_theorem_using(
                &PointOperationView::from_point(context),
                application,
                surface_premises,
            ),
            // A focused function-outcome goal applies theorems through the
            // point checker, reading its data from the goal; the effect
            // context is the replay-level set the legacy drain consumed.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view_with_effects(OutcomeEffectContext::Replay)
                    .expect("a focused outcome judgment resolves its point view");
                self.apply_point_theorem_using(&view, application, surface_premises)
            }
            ProofContext::Execution(context) => {
                self.apply_execution_theorem_using(context, application, surface_premises)
            }
        }
    }

    fn apply_pure_theorem_using(
        &self,
        context: &PureProofContext<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "`apply using` premise"))
            .collect::<Result<Vec<_>, _>>()?;

        for premise in &explicit_premises {
            if !self.facts().contains(premise) {
                return Err(self.step_error(format!(
                    "`apply using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        // The checker receives exactly the named premises, not the ambient
        // context. Its work is therefore independent of unrelated facts, and
        // it cannot silently search for an omitted theorem requirement.
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let program_point_states = ProgramPointStates::new();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            pre_state: &state,
            post_state: &state,
            result: None,
            program_point_states: &program_point_states,
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let applied = apply_theorem_applications_to_available(
            context.theorem_environment,
            &[(self.node.depth, application.clone())],
            context.claim_label,
            None,
            explicit_premises,
            &application_context,
            context.predicate_environment,
            context.click_function_environment,
            &unfolded_predicates,
        )?;

        let mut facts = self.facts().clone();
        let mut added_facts = Vec::new();
        for fact in applied {
            if !facts.contains(&fact) {
                added_facts.push(fact.clone());
            }
            facts = facts.with_fact(fact);
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, facts),
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
        })
    }

    fn apply_point_theorem_using(
        &self,
        view: &PointOperationView<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let checked = check_point_theorem_application_using_facts(
            view.theorem_environment,
            application,
            surface_premises,
            view.claim_label,
            view.tactic_index,
            &self.facts(),
            view.parameters,
            view.arguments,
            view.pre_state,
            view.state,
            view.result,
            view.program_point_states,
            view.surface_propositions,
            &unfolded_predicates,
            view.effect_facts,
            view.predicate_environment,
            view.click_function_environment,
            false,
        )?;
        let complete = self.goal().is_some_and(|goal| checked.facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, checked.facts),
            checked_facts: Arc::new(checked.added_facts.clone()),
            added_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_execution_theorem_using(
        &self,
        context: &ExecutionProofContext<'a>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        let retain_function_entry_derivation = execution
            .replay
            .frontier
            .execution_start_state
            .as_ref()
            .is_none_or(|start| start == &*execution.state);
        let checked = check_point_theorem_application_using_facts(
            context.theorem_environment,
            application,
            surface_premises,
            context.claim_label,
            context.tactic_index,
            &self.facts(),
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            &execution.state,
            None,
            &execution.replay.program_point_states,
            &execution.replay.surface_propositions,
            &execution.replay.unfolded_predicates,
            &execution.replay.effect_facts,
            context.predicate_environment,
            context.click_function_environment,
            retain_function_entry_derivation,
        )?;
        if let Some(prerequisite) = checked.function_entry_prerequisite
            && !execution
                .replay
                .function_entry_execution_prerequisites
                .contains(&prerequisite)
        {
            execution
                .last_step_delta
                .function_entry_prerequisites
                .push(prerequisite.clone());
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(prerequisite);
        }
        if let Some(derivation) = checked.function_entry_derivation
            && !execution
                .replay
                .function_entry_derivations
                .contains(&derivation)
        {
            execution
                .last_step_delta
                .function_entry_derivations
                .push(derivation.clone());
            execution
                .replay
                .function_entry_derivations
                .insert(derivation);
        }
        let complete = self.goal().is_some_and(|goal| checked.facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.discharged_if_or_execution_at(
                self.focused,
                complete,
                checked.facts,
                execution,
            ),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_point_choose(&self, choice: &ProofChoice) -> Result<ProofState, ClickError> {
        let view = match self.context.as_ref() {
            ProofContext::Point(context) => PointOperationView::from_point(context),
            // A choice on a judgment stated at a function outcome selects
            // its requirement source through the outcome view.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => self
                .outcome_point_view()
                .expect("a focused outcome judgment resolves its point view"),
            ProofContext::Execution(_) => self
                .execution_proposition_point_view()
                .ok_or_else(|| self.step_error("`choose` requires a point proposition proof"))?,
            _ => return Err(self.step_error("`choose` requires a point proposition proof")),
        };
        self.proposition_goal("`choose` requires a proposition goal")?;
        if choice.name == "result"
            || view.state.locals().contains_name(&choice.name)
            || self.state.locals.values.contains_key(&choice.name)
        {
            return Err(self.step_error(format!("`{}` is already in scope", choice.name)));
        }

        let source_index = match &choice.source {
            ProofFactSource::Requirement(index) => {
                if *index >= view.original_requirements.len() {
                    return Err(self.step_error(format!(
                        "requirement {index} is out of range; function has {} requirement(s)",
                        view.original_requirements.len()
                    )));
                }
                *index
            }
            ProofFactSource::RequirementLabel(label) => view
                .requirement_label_indices
                .and_then(|indices| indices.get(label))
                .copied()
                .ok_or_else(|| self.step_error(format!("unknown requirement label `{label}`")))?,
        };
        let mut source = view
            .requirement_facts
            .get(source_index)
            .cloned()
            .ok_or_else(|| {
                self.step_error(format!("requirement {source_index} was not available"))
            })?;
        let unfolded_predicates = self.active_unfolded_predicates();
        if !matches!(source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty() {
            source = unfold_predicates_in_proposition(
                view.predicate_environment,
                view.click_function_environment,
                &unfolded_predicates,
                &source,
                self.facts().assumptions(),
            )
            .map_err(|message| self.step_error(message))?;
        }
        let Proposition::Exists {
            var, sort, body, ..
        } = source
        else {
            return Err(self.step_error("`choose` source is not an existential proposition"));
        };
        if sort != Sort::CInt32 {
            return Err(self.step_error("only int32 existential choices are supported"));
        }

        let chosen = Bitvector32Term::Variable(Variable(self.state.locals.next_choice_variable));
        let chosen_fact = substitute_int32_variable_in_proposition(&body, var, chosen.clone());
        let mut locals = self.state.locals.clone();
        locals.values = locals.values.with_inserted(
            choice.name.clone(),
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(chosen))),
        );
        locals.next_choice_variable += 1;
        let added_facts = (!self.facts().contains_top_level(&chosen_fact))
            .then(|| vec![chosen_fact.clone()])
            .unwrap_or_default();
        let facts = self.facts().with_fact(chosen_fact.clone());
        Ok(ProofState {
            locals,

            goals: self.state.goals.with_facts_at(self.focused, facts),
            added_facts: Arc::new(added_facts),
            checked_facts: Arc::new(vec![chosen_fact]),
        })
    }

    fn apply_point_witness(&self, witness: &ProofWitness) -> Result<ProofState, ClickError> {
        let view = match self.context.as_ref() {
            ProofContext::Point(context) => PointOperationView::from_point(context),
            // A witness refinement on a judgment stated at a function
            // outcome reads the outcome's result-aware data.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => self
                .outcome_point_view()
                .expect("a focused outcome judgment resolves its point view"),
            ProofContext::Execution(_) => self
                .execution_proposition_point_view()
                .ok_or_else(|| self.step_error("`witness` requires a point proposition proof"))?,
            _ => return Err(self.step_error("`witness` requires a point proposition proof")),
        };
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = unfold_predicates_in_proposition(
            view.predicate_environment,
            view.click_function_environment,
            &unfolded_predicates,
            &goal,
            self.facts().assumptions(),
        )
        .map_err(|message| self.step_error(format!("could not unfold witness goal: {message}")))?;
        let values = parameter_values(view.parameters, view.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(view.parameters, &values, view.state.memory());
        let (values, array_refs) = contract_environment_at_state(&values, &array_refs, view.state);
        let checked_witness = ProofWitness {
            name: witness.name.clone(),
            value: self.substitute_point_locals_in_expression(&witness.value)?,
        };
        let value = evaluate_witness_tactic_value(
            &checked_witness,
            view.claim_label,
            0,
            view.tactic_index,
            &values,
            &array_refs,
            view.pre_state,
            view.state,
            view.result,
            self.facts().assumptions(),
            view.predicate_environment,
            view.click_function_environment,
            view.program_point_states,
        )?;
        let goal = apply_witness_tactic(
            &checked_witness,
            value,
            goal,
            view.claim_label,
            0,
            view.tactic_index,
        )?;
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Exists { name, body, .. }) if name == &witness.name => {
                let substitutions = BTreeMap::from([(name.clone(), witness.value.clone())]);
                Some(
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface witness goal: {message}"
                        ))
                    })?,
                )
            }
            Some(ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            }) if item == &witness.name => {
                let substitutions = BTreeMap::from([(item.clone(), witness.value.clone())]);
                let start =
                    substitute_contract_expression(start, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range start: {message}"
                        ))
                    })?;
                let end =
                    substitute_contract_expression(end, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range end: {message}"
                        ))
                    })?;
                let value = substitute_contract_expression(&witness.value, &substitutions)
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range witness: {message}"
                        ))
                    })?;
                let body =
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range witness goal: {message}"
                        ))
                    })?;
                Some(ClickProposition::And(
                    Box::new(ClickProposition::And(
                        Box::new(ClickProposition::Comparison {
                            left: start,
                            operator: ComparisonOperator::LessEqual,
                            right: value.clone(),
                        }),
                        Box::new(ClickProposition::Comparison {
                            left: value,
                            operator: ComparisonOperator::LessThan,
                            right: end,
                        }),
                    )),
                    Box::new(body),
                ))
            }
            _ => None,
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(self.focused, {
                let context = self.refined_context(self.facts().clone());
                self.refined_proposition(context, goal, surface_goal)
            }),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    fn apply_point_instantiate_using(
        &self,
        surface_quantified: &ClickProposition,
        argument: &ContractExpression,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let view = match self.context.as_ref() {
            ProofContext::Point(context) => PointOperationView::from_point(context),
            // An instantiation on a judgment stated at a function outcome
            // evaluates its argument and quantified fact in that outcome's
            // result-aware point environment.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => self
                .outcome_point_view()
                .expect("a focused outcome judgment resolves its point view"),
            // A leading nested `have` is a proposition proof at the
            // execution frontier. It evaluates the quantified fact and
            // argument in that frontier's point environment without
            // exporting or replaying execution state.
            ProofContext::Execution(_) => {
                self.execution_proposition_point_view().ok_or_else(|| {
                    self.step_error("`instantiate` requires a point proposition proof")
                })?
            }
            _ => {
                return Err(self.step_error("`instantiate` requires a point proposition proof"));
            }
        };
        self.proposition_goal("`instantiate` requires a proposition goal")?;

        let explicit_premises = surface_premises
            .iter()
            .map(|surface| self.lower_surface_proposition(surface, "`instantiate using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        for premise in &explicit_premises {
            if !self.facts().replay_available_across_effects(premise, &[]) {
                return Err(self.step_error(format!(
                    "`instantiate using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        let lowered_quantified =
            self.lower_surface_proposition(surface_quantified, "`instantiate` quantified fact")?;
        let quantified = if self.facts().contains(&lowered_quantified) {
            lowered_quantified
        } else if let Some(available) = self
            .facts()
            .matching_quantified_replay_fact(&lowered_quantified)
        {
            available
        } else {
            return Err(self.step_error(format!(
                "`instantiate` quantified fact is not exactly available: {}",
                describe_click_proposition(surface_quantified)
            )));
        };

        let parameter_values = parameter_values(view.parameters, view.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs =
            array_refs_for_parameters(view.parameters, &parameter_values, view.state.memory());
        let (values, array_refs) =
            contract_environment_at_state(&parameter_values, &array_refs, view.state);
        let mut active_functions = BTreeSet::new();
        let argument = self.substitute_point_locals_in_expression(argument)?;
        let value = evaluate_contract_expression_with_environment(
            &values,
            &array_refs,
            view.pre_state,
            view.state,
            view.result,
            self.facts().assumptions(),
            &argument,
            view.predicate_environment,
            view.click_function_environment,
            view.program_point_states,
            &mut active_functions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not evaluate `instantiate` argument: {message}"
            ))
        })?;
        let CValue::Int32(argument) = value else {
            return Err(self.step_error("`instantiate` argument did not evaluate to int32"));
        };

        let conclusion =
            check_forall_int32_instantiation(&quantified, argument, &explicit_premises)
                .map_err(|message| self.step_error(format!("`instantiate` failed: {message}")))?;
        let added = !self.facts().contains_top_level(&conclusion);
        let facts = self.facts().with_fact(conclusion.clone());
        let added_facts = added.then_some(conclusion).into_iter().collect::<Vec<_>>();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.with_facts_at(self.focused, facts),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    fn apply_rewrite(&self, surface_equality: &ClickProposition) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.apply_pure_rewrite(surface_equality),
            ProofContext::Point(context) => {
                self.apply_point_rewrite(&PointOperationView::from_point(context), surface_equality)
            }
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view()
                    .expect("a focused outcome judgment resolves its point view");
                self.apply_point_rewrite(&view, surface_equality)
            }
            // A nested execution `have` is still a proposition proof. It
            // borrows the execution context only for lowering; its scope join
            // restores the exact outer frontier after this checked rewrite.
            ProofContext::Execution(_) if self.goal().is_some() => {
                self.apply_pure_rewrite(surface_equality)
            }
            ProofContext::Execution(_) => {
                Err(self.step_error("`rewrite` requires a proposition proof"))
            }
        }
    }

    // Keep lowering's large proposition temporaries out of the common rewrite
    // dispatcher frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    fn apply_pure_rewrite(
        &self,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let goal = Box::new(
            self.proposition_goal("`rewrite` requires a proposition goal")?
                .clone(),
        );
        let equality =
            Box::new(self.lower_surface_proposition(surface_equality, "`rewrite` equality")?);
        self.finish_rewrite(goal, equality, surface_equality)
    }

    // Keep point-lowering and unfold temporaries out of the common rewrite
    // dispatcher frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    fn apply_point_rewrite(
        &self,
        view: &PointOperationView<'_>,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = Box::new(
            unfold_predicates_in_proposition(
                view.predicate_environment,
                view.click_function_environment,
                &unfolded_predicates,
                self.proposition_goal("`rewrite` requires a proposition goal")?,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` goal: {message}"))
            })?,
        );
        let recorded = view
            .surface_propositions
            .available_kernel_matching(surface_equality, |kernel| {
                self.facts().materialization_available(kernel)
            })
            .map(|kernel| Box::new(kernel.clone()))
            .or_else(|| {
                let reverse = reverse_surface_equality(surface_equality)?;
                let kernel = view
                    .surface_propositions
                    .available_kernel_matching(&reverse, |kernel| {
                        self.facts().materialization_available(kernel)
                    })?
                    .clone();
                reverse_kernel_equality(kernel).map(Box::new)
            });
        let equality = match recorded {
            Some(equality) => equality,
            None => Box::new(
                lower_point_proposition_with_assumptions(
                    surface_equality,
                    self.facts().assumptions(),
                    view.parameters,
                    view.arguments,
                    view.pre_state,
                    view.state,
                    view.result,
                    view.program_point_states,
                    view.predicate_environment,
                    view.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower `rewrite` equality: {message}"))
                })?,
            ),
        };
        let equality = Box::new(
            unfold_predicates_in_proposition(
                view.predicate_environment,
                view.click_function_environment,
                &unfolded_predicates,
                &equality,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` equality: {message}"))
            })?,
        );
        self.finish_rewrite(goal, equality, surface_equality)
    }

    // Keep the by-value goal/equality pair in the rewrite worker rather than
    // every caller's frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    fn finish_rewrite(
        &self,
        goal: Box<Proposition>,
        equality: Box<Proposition>,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let admitted = self.facts().materialization_available(&equality)
            || reverse_kernel_equality(equality.as_ref().clone())
                .as_ref()
                .is_some_and(|reverse| self.facts().materialization_available(reverse));
        let available = if admitted {
            std::slice::from_ref(equality.as_ref())
        } else {
            &[]
        };
        let rewritten = rewrite_proposition_by_exact_equality(&goal, &equality, available)
            .map_err(|message| self.step_error(message))?;
        let surface_goal = self.surface_goal().and_then(|surface_goal| {
            let candidate =
                rewrite_click_proposition_by_surface_equality(surface_goal, surface_equality)?;
            self.lower_surface_proposition_direct(&candidate, "rewritten Surface goal")
                .ok()
                .filter(|lowered| lowered == &rewritten)
                .map(|_| candidate)
        });
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_at(self.focused, {
                let context = self.refined_context(self.facts().clone());
                self.refined_proposition(context, rewritten, surface_goal)
            }),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    fn apply_extract(&self, surface: &ClickProposition) -> Result<ProofState, ClickError> {
        let proposition = self.lower_surface_proposition(surface, "`extract` proposition")?;
        if !self.facts().contains_proper_conjunct(&proposition)
            && !self
                .facts()
                .contains_discharged_implication_consequent(&proposition)
        {
            return Err(self.step_error(format!(
                "`extract` proposition is not a proper conjunct of an exact available fact or a discharged implication consequent: {}",
                describe_pure_fact(&proposition, &[], &[])
            )));
        }
        let added_facts = (!self.facts().contains_top_level(&proposition))
            .then(|| proposition.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let facts = self.facts().with_fact(proposition);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, facts),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    /// The point-operation data a result-aware checker consumes, resolved
    /// either from a point proof's borrowed context or from a focused
    /// function-outcome goal on an execution proof. This is the goal-aware
    /// point view: outcome goals own their result, post-state, surface
    /// lowerings, and effect facts, and borrow the frontier snapshot for the
    /// remaining program-point data.
    fn outcome_point_view(&self) -> Option<PointOperationView<'_>> {
        self.outcome_point_view_with_effects(OutcomeEffectContext::Path)
    }

    /// Point-operation data for a proposition scope opened on an execution
    /// frontier before a function outcome exists. The nested goal borrows the
    /// frontier snapshot solely for lowering and requirement selection;
    /// checked point steps can refine only that proposition and proof-local
    /// bindings.
    fn execution_proposition_point_view(&self) -> Option<PointOperationView<'_>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let Goal::Proposition(goal) = self.focused_goal()? else {
            return None;
        };
        if goal.outcome.is_some() {
            return None;
        }
        let execution = goal.context.execution.as_deref()?;
        Some(PointOperationView {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: &execution.replay.effect_facts,
            parameters: context.parsed_function.parameters(),
            arguments: context.arguments,
            pre_state: execution.replay.execution_start_state(&execution.state),
            state: &execution.state,
            result: None,
            program_point_states: &execution.replay.program_point_states,
            surface_propositions: &execution.replay.surface_propositions,
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
            theorem_environment: context.theorem_environment,
            original_requirements: context.function_block.requires(),
            requirement_label_indices: Some(context.function_block.requirement_label_indices()),
            requirement_facts: &execution.replay.execution_start_facts,
        })
    }

    /// The focused judgment's result-aware point data: a function-outcome
    /// goal owns its data, and a proposition judgment stated at an outcome
    /// borrows that outcome's data by identity.
    fn focused_outcome_point(&self) -> Option<&Arc<OutcomePointData>> {
        match self.focused_goal()? {
            Goal::FunctionOutcome(goal) => Some(&goal.point),
            Goal::Proposition(goal) => goal.outcome.as_ref(),
            Goal::Frontier(_) => None,
        }
    }

    /// Decides one explicit post-execution `if` from the focused outcome's
    /// exact fact context. The syntax driver may use the returned polarity to
    /// choose which source arm to visit, but it cannot manufacture a fact or
    /// successor: both alternatives are lowered and the kernel assumptions
    /// must establish exactly one of them on this `Proof` path.
    pub(super) fn checked_outcome_if_value(
        &self,
        condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        if !matches!(self.focused_goal(), Some(Goal::FunctionOutcome(_))) {
            return Err(self.step_error("post-execution `if` requires a focused outcome goal"));
        }
        let point = self
            .focused_outcome_point()
            .expect("a focused outcome judgment resolves its point data");
        let mut recorded_value = None;
        for decision in point.branch_decisions.iter() {
            if &decision.condition != condition {
                continue;
            }
            if recorded_value.is_some_and(|value| value != decision.value) {
                return Err(self.step_error(
                    "focused outcome records both sides of the post-execution `if` condition",
                ));
            }
            recorded_value = Some(decision.value);
        }
        if let Some(value) = recorded_value {
            return Ok(value);
        }
        let negative_surface = ClickProposition::Not(Box::new(condition.clone()));
        let positive =
            self.lower_surface_proposition(condition, "post-execution `if` condition")?;
        let negative =
            self.lower_surface_proposition(&negative_surface, "post-execution `if` negation")?;
        let assumptions = self.facts().assumptions();
        let positive_holds = self.facts().contains(&positive) || assumptions.proves(&positive);
        let negative_holds = self.facts().contains(&negative)
            || assumptions.proves(&negative)
            || fact_conflicts_with_assumptions(&positive, assumptions);
        match (positive_holds, negative_holds) {
            (true, false) => Ok(true),
            (false, true) => Ok(false),
            (false, false) => Err(self
                .step_error("focused outcome does not decide the post-execution `if` condition")),
            (true, true) => Err(self.step_error(
                "focused outcome proves both sides of the post-execution `if` condition",
            )),
        }
    }

    /// Reports whether every checked execution path already decides a
    /// post-execution condition. Such an `if` is a cursor over an existing
    /// path partition and may be deferred until each outcome Proof is
    /// focused. An undecided logical case split must stay with the general
    /// proof driver, which introduces the two assumptions explicitly.
    pub(super) fn post_execution_if_is_path_decided(
        &self,
        condition: &ClickProposition,
    ) -> Result<bool, ClickError> {
        self.require_execution_frontier("post-execution `if`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("post-execution `if` lost its execution frontier"))?;
        if !execution.replay.is_at_function_exit() {
            return Err(self.step_error("post-execution `if` requires function exit"));
        }
        let checked = execution
            .replay
            .execution()
            .ok_or_else(|| self.step_error("post-execution `if` has no checked execution paths"))?;
        for path_index in 0..checked.paths().len() {
            check_verification_deadline()?;
            let decisions = execution
                .outcome_branch_decisions
                .get(path_index)
                .unwrap_or(&execution.branch_decisions);
            let mut recorded = None;
            for decision in decisions.iter() {
                if &decision.condition != condition {
                    continue;
                }
                if recorded.is_some_and(|value| value != decision.value) {
                    return Err(self.step_error(
                        "checked execution path records both sides of the post-execution `if` condition",
                    ));
                }
                recorded = Some(decision.value);
            }
            if recorded.is_none() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Resolves the view with the caller's effect-availability context: the
    /// transport checker consumes the path's own execution facts, while the
    /// theorem checker consumes the replay-level effect set, matching the
    /// legacy drain inputs exactly.
    fn outcome_point_view_with_effects(
        &self,
        effects: OutcomeEffectContext,
    ) -> Option<PointOperationView<'_>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let point = self.focused_outcome_point()?;
        let goal = self.focused_goal()?;
        let execution = goal.context().execution.as_deref()?;
        Some(PointOperationView {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: match effects {
                OutcomeEffectContext::Path => point.effect_facts.as_ref(),
                OutcomeEffectContext::Replay => &execution.replay.effect_facts,
            },
            parameters: context.parsed_function.parameters(),
            arguments: context.arguments,
            pre_state: execution.replay.execution_start_state(&execution.state),
            state: &point.state,
            result: Some(point.result.as_ref()),
            program_point_states: &execution.replay.program_point_states,
            surface_propositions: &point.surface_propositions,
            predicate_environment: context.predicate_environment,
            click_function_environment: context.click_function_environment,
            theorem_environment: context.theorem_environment,
            original_requirements: context.function_block.requires(),
            requirement_label_indices: Some(context.function_block.requirement_label_indices()),
            requirement_facts: point.requirement_facts.as_ref(),
        })
    }

    fn apply_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Point(context) => self.apply_point_transport_using(
                source,
                target,
                premises,
                &PointOperationView::from_point(context),
            ),
            // A focused function-outcome goal transports result-aware facts
            // through the same point checker, reading its data from the goal.
            ProofContext::Execution(_) if self.focused_outcome_point().is_some() => {
                let view = self
                    .outcome_point_view()
                    .expect("a focused outcome judgment resolves its point view");
                self.apply_point_transport_using(source, target, premises, &view)
            }
            ProofContext::Execution(context) => {
                self.apply_execution_transport_using(source, target, premises, context)
            }
            ProofContext::Pure(_) => {
                Err(self.step_error("`transport using` requires a point or execution proof"))
            }
        }
    }

    fn apply_point_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        view: &PointOperationView<'_>,
    ) -> Result<ProofState, ClickError> {
        let (source, target, premises) = if premises.is_empty() {
            (source.clone(), target.clone(), premises.to_vec())
        } else {
            (
                self.substitute_goal_surface_bindings_in_proposition(source)?,
                self.substitute_goal_surface_bindings_in_proposition(target)?,
                premises
                    .iter()
                    .map(|premise| self.substitute_goal_surface_bindings_in_proposition(premise))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        };
        let checked = check_point_fact_transport_using_facts(
            &source,
            &target,
            &premises,
            view.claim_label,
            view.tactic_index,
            &self.facts(),
            view.effect_facts,
            view.parameters,
            view.arguments,
            view.pre_state,
            view.state,
            view.result,
            view.program_point_states,
            view.surface_propositions,
            view.predicate_environment,
            view.click_function_environment,
        )?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        let checked_facts = vec![checked.source, checked.target.clone()];
        facts = facts.with_fact(checked.target);
        // A focused outcome goal records the checker-owned source and target
        // lowerings atomically with its fact successor; the drain no longer
        // has to re-record them into a caller-owned map for this path.
        if let Some(Goal::FunctionOutcome(goal)) = self.focused_goal() {
            let mut updated = goal.clone();
            let mut point = (*updated.point).clone();
            point
                .surface_propositions
                .record_lowering(&source, &checked_facts[0])?;
            point
                .surface_propositions
                .record_lowering(&target, &checked_facts[1])?;
            updated.point = Arc::new(point);
            updated.context = GoalContext {
                facts,
                unfolded_predicates: goal.context.unfolded_predicates.clone(),
                execution: goal.context.execution.clone(),
            };
            return Ok(ProofState {
                locals: self.state.locals.clone(),
                goals: self
                    .state
                    .goals
                    .replace_at(self.focused, Goal::FunctionOutcome(updated)),
                added_facts: Arc::new(added_facts),
                checked_facts: Arc::new(checked_facts),
            });
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self
                .state
                .goals
                .discharged_if_at(self.focused, complete, facts),
            added_facts: Arc::new(added_facts),
            checked_facts: Arc::new(checked_facts),
        })
    }

    fn apply_execution_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        context: &ExecutionProofContext<'a>,
    ) -> Result<ProofState, ClickError> {
        // A nested proposition proof stated at this frontier may transport
        // facts as well; the successor below preserves the goal's kind.
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let pre_state = execution
            .replay
            .old_reference_state(&execution.state)
            .clone();
        let checked = check_point_fact_transport_using_facts(
            source,
            target,
            premises,
            context.claim_label,
            context.tactic_index,
            &self.facts(),
            &execution.replay.effect_facts,
            context.parsed_function.parameters(),
            context.arguments,
            &pre_state,
            &execution.state,
            None,
            &execution.replay.program_point_states,
            &execution.replay.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
        )?;
        execution
            .replay
            .surface_propositions
            .record_lowering(source, &checked.source)?;
        execution
            .replay
            .surface_propositions
            .record_lowering(target, &checked.target)?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        facts = facts.with_fact(checked.target);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.discharged_if_or_execution_at(
                self.focused,
                complete,
                facts,
                execution,
            ),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    fn apply_execution_statement_step(
        &self,
        step: SimpleProofStep,
        premises: &[ClickProposition],
    ) -> Result<Self, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`step using` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`step using`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let checked = check_step_using_facts(
            &mut execution.replay,
            &mut execution.state,
            &self.facts(),
            premises,
            context.function_block,
            context.function,
            context.parsed_function,
            context.arguments,
            context.function_environment,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        let Some(Goal::Frontier(frontier)) = self.focused_goal() else {
            unreachable!("the frontier requirement was checked above");
        };
        let parent_execution = Arc::new(execution.clone());
        let execution_start_state = execution
            .replay
            .execution_start_state(&execution.state)
            .clone();
        let initial_continuation_depth = execution.replay.frontier.continuations.len();
        let make_goal = |checked: CheckedStatementStep| {
            let mut successor_execution = execution.clone();
            successor_execution.replay = checked.replay;
            successor_execution.state = checked.state.into();
            (
                Goal::Frontier(FrontierGoal {
                    selection: frontier.selection,
                    context: GoalContext {
                        facts: checked.facts,
                        unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                        execution: Some(Arc::new(successor_execution)),
                    },
                }),
                checked.added_facts,
                checked.path,
            )
        };

        let (goals, focused, added_facts) = match checked.len() {
            1 => {
                let (goal, added, path) = make_goal(
                    checked
                        .into_iter()
                        .next()
                        .expect("one checked successor was required"),
                );
                debug_assert!(path.is_none());
                (
                    self.state.goals.replace_at(self.focused, goal),
                    self.focused,
                    added,
                )
            }
            2 => {
                let mut by_polarity = [None, None];
                let mut condition = None;
                let mut common_added: Option<Vec<Proposition>> = None;
                for successor in checked {
                    let CheckedStatementStep {
                        replay,
                        state,
                        facts,
                        added_facts: added,
                        path,
                    } = successor;
                    let Some((path_condition, value)) = path else {
                        return Err(self
                            .step_error("statement successors omitted their certified partition"));
                    };
                    if let Some(condition) = &condition {
                        if condition != &path_condition {
                            return Err(self.step_error(
                                "statement successors used different partition conditions",
                            ));
                        }
                    } else {
                        condition = Some(path_condition.clone());
                    }
                    let slot = usize::from(!value);
                    let mut successor_execution = execution.clone();
                    successor_execution.replay = replay;
                    successor_execution.state = state.into();
                    let path_fact = Proposition::ConditionIs(path_condition, value);
                    if by_polarity[slot]
                        .replace((facts, Arc::new(successor_execution), vec![path_fact]))
                        .is_some()
                    {
                        return Err(
                            self.step_error("statement successors repeated one partition polarity")
                        );
                    }
                    if let Some(common) = &mut common_added {
                        common.retain(|fact| added.contains(fact));
                    } else {
                        common_added = Some(added);
                    }
                }
                let [Some(then_arm), Some(else_arm)] = by_polarity else {
                    return Err(self.step_error(
                        "statement successors did not cover both partition polarities",
                    ));
                };
                let condition = condition.expect("two successors recorded a condition");
                let common_added = common_added.unwrap_or_default();
                // Both call successors descend from the pre-call facts, but
                // their statement batches are siblings even when those
                // batches contain some equal propositions. Keep the actual
                // shared ancestor here; the terminal merge computes common
                // post-call facts output-sensitively from the two arm deltas.
                let common_facts = self.facts().clone();
                let split = SplitId(self.state.goals.next_id);
                let ids = [
                    GoalId(self.state.goals.next_id + 1),
                    GoalId(self.state.goals.next_id + 2),
                ];
                let partition = Arc::new(StatementSuccessorPartition {
                    split,
                    ids,
                    condition,
                    base_facts: [then_arm.0.clone(), else_arm.0.clone()],
                    base_executions: [then_arm.1.clone(), else_arm.1.clone()],
                    path_facts: [then_arm.2, else_arm.2],
                    common_facts,
                    parent_unfolds: frontier.context.unfolded_predicates.clone(),
                    parent_execution: parent_execution.clone(),
                    execution_start_state: execution_start_state.clone(),
                    initial_continuation_depth,
                });
                let goals = self.state.goals.split_at(
                    self.focused,
                    [
                        Goal::Frontier(FrontierGoal {
                            selection: frontier.selection,
                            context: GoalContext {
                                facts: then_arm.0,
                                unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                                execution: Some(Arc::new({
                                    let mut execution = (*then_arm.1).clone();
                                    execution.last_step_delta.statement_partition =
                                        Some(partition.clone());
                                    execution
                                })),
                            },
                        }),
                        Goal::Frontier(FrontierGoal {
                            selection: frontier.selection,
                            context: GoalContext {
                                facts: else_arm.0,
                                unfolded_predicates: frontier.context.unfolded_predicates.clone(),
                                execution: Some(Arc::new({
                                    let mut execution = (*else_arm.1).clone();
                                    execution.last_step_delta.statement_partition = Some(partition);
                                    execution
                                })),
                            },
                        }),
                    ],
                );
                debug_assert_eq!(goals.0, split);
                debug_assert_eq!(goals.1, ids);
                let goals = goals.2;
                (goals, ids[0], common_added)
            }
            count => {
                return Err(self.step_error(format!(
                    "statement execution produced {count} certified successors; expected one successor or one binary partition"
                )));
            }
        };
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                goals,
                added_facts: Arc::new(added_facts.clone()),
                checked_facts: Arc::new(added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused: self.focused,
                depth: self.node.depth + 1,
            }),
            focused,
        })
    }

    fn apply_execution_mark(&self, name: &str) -> Result<ProofState, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`mark` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`mark`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let point = ProgramPointRef {
            region: CodeRegionRef::Mark(name.to_string()),
            kind: ProgramPointKind::Entry,
        };
        if execution.replay.program_point_states.contains_key(&point) {
            return Err(self.step_error(format!("duplicate proof mark `{name}`")));
        }
        execution
            .replay
            .program_point_states
            .insert(point, (*execution.state).clone());
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_frontier_at(
                self.focused,
                self.facts().clone(),
                execution,
            ),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    fn apply_close_invariants(&self) -> Result<ProofState, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`close_invariants` requires an execution-frontier proof"));
        }
        self.require_execution_frontier("`close_invariants`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if !execution.replay.loop_invariant_region {
            return Err(
                self.step_error("`close_invariants` is only available in a loop-region proof")
            );
        }
        if execution.replay.region_invariants_closed {
            return Err(
                self.step_error("the invariant bundle was closed more than once on one path")
            );
        }
        execution.replay.region_invariants_closed = true;
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.replace_frontier_at(
                self.focused,
                self.facts().clone(),
                execution,
            ),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Checks the complete loop-invariant bundle at this back edge and
    /// retains `close_invariants` when the source path has not already
    /// supplied it.
    ///
    /// The legacy source driver may arrive with the surface closer already
    /// reflected in cursor metadata. That metadata is not authority for the
    /// invariant judgment: this operation always performs the kernel check
    /// against the Proof-owned state and facts before accepting the path.
    pub(super) fn certify_loop_invariant_bundle(
        &self,
        loop_entry_state: &CState,
        invariant_checks: &[CLoopInvariantCheck],
    ) -> Result<Self, ClickError> {
        if !matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("loop invariant closure requires an execution proof"));
        }
        self.require_execution_frontier("loop invariant closure")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("loop invariant closure lost its execution state"))?;
        if !execution.replay.loop_invariant_region {
            return Err(self.step_error("loop invariant closure requires a loop-region proof"));
        }

        let mut closer_facts = self.facts().to_vec();
        closer_facts.extend(
            execution
                .replay
                .effect_facts
                .iter()
                .map(|fact| fact.proposition().clone()),
        );
        closer_facts.extend(crate::kernel::certified_store_equations(
            &execution.replay.effect_facts,
        ));
        c_loop_invariants_hold_at_back_edge_using(
            &execution.state,
            loop_entry_state,
            invariant_checks,
            &assumptions_from_propositions(&closer_facts),
        )
        .map_err(|message| self.step_error(format!("invariant bundle: {message}")))?;

        if execution.replay.region_invariants_closed {
            Ok(self.clone())
        } else {
            self.apply_step(SimpleProofStep::CloseInvariants)
        }
    }

    fn apply_contradiction(&self, surface: &ClickProposition) -> Result<ProofState, ClickError> {
        let fact = self.lower_surface_proposition(surface, "`contradiction` fact")?;
        let negated = Proposition::Not(Box::new(fact.clone()));
        let opposite_condition = match &fact {
            Proposition::ConditionIs(condition, value) => {
                Some(Proposition::ConditionIs(condition.clone(), !value))
            }
            _ => None,
        };
        if !self.facts().contains(&fact)
            || (!self.facts().contains(&negated)
                && !opposite_condition
                    .as_ref()
                    .is_some_and(|opposite| self.facts().contains(opposite)))
        {
            return Err(self.step_error(format!(
                "`contradiction` requires an exact fact and its exact negation or opposite condition polarity: {fact:?}"
            )));
        }
        Ok(self.closed_state())
    }

    fn proposition_goal(&self, message: &str) -> Result<&Proposition, ClickError> {
        self.goal().ok_or_else(|| self.step_error(message))
    }

    fn require_execution_frontier(&self, operation: &str) -> Result<(), ClickError> {
        (matches!(self.focused_goal(), Some(Goal::Frontier(_)))
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
        self.goal_execution()
            .and_then(|execution| execution.replay.loop_effect_goal.as_ref())
            .is_some_and(|goal| goal.closed)
    }

    fn closed_state(&self) -> ProofState {
        ProofState {
            locals: self.state.locals.clone(),

            goals: self.state.goals.discharge_at(self.focused),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        }
    }

    fn step_error(&self, message: impl Into<String>) -> ClickError {
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

/// The source-level form of one simple step, for diagnostics that point
/// at a line the user wrote.
fn simple_step_source_name(step: &SimpleProofStep) -> &'static str {
    match step {
        SimpleProofStep::Assumption => "assumption()",
        SimpleProofStep::Normalize => "normalize()",
        SimpleProofStep::Intro => "intro()",
        SimpleProofStep::Split => "split()",
        SimpleProofStep::Left => "left()",
        SimpleProofStep::Right => "right()",
        SimpleProofStep::Enumerate => "enumerate()",
        SimpleProofStep::Step | SimpleProofStep::StepUsing(_) => "step",
        SimpleProofStep::ApplyTheoremUsing { .. } => "apply",
        SimpleProofStep::TransportUsing { .. } => "transport",
        SimpleProofStep::InstantiateUsing { .. } => "instantiate",
        SimpleProofStep::Have { .. } => "have",
        SimpleProofStep::Rewrite(_) => "rewrite",
        SimpleProofStep::Extract(_) => "extract",
        SimpleProofStep::Contradiction(_) => "contradiction",
        SimpleProofStep::Witness(_) => "witness",
        SimpleProofStep::Choose(_) => "choose",
        SimpleProofStep::UnfoldPredicate(_) | SimpleProofStep::UnfoldResource(_) => "unfold",
        SimpleProofStep::FoldResource(_) => "fold",
        SimpleProofStep::ObserveResource(_) => "observe",
        SimpleProofStep::FrameUsing { .. } => "frame",
        SimpleProofStep::CloseInvariants => "close_invariants()",
        SimpleProofStep::Mark(_) => "mark",
        _ => "tactic",
    }
}

impl<'a> ProofScope<'a> {
    pub(super) fn is_complete(&self) -> bool {
        self.body.is_complete() || self.body.focused_loop_effect_closed()
    }

    #[cfg(test)]
    pub(super) fn body(&self) -> &Proof<'a> {
        &self.body
    }

    /// Attributes the next checked execution operation inside this scope to
    /// its own source tactic without changing the enclosing scope root.
    pub(super) fn with_execution_tactic_index(
        &self,
        tactic_index: usize,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.body = self.body.with_execution_tactic_index(tactic_index)?;
        Ok(next)
    }

    /// Opens another composite resource from this scope's current checked
    /// body. The returned nested scope can only rejoin through `join_nested`,
    /// which checks that it descends from this exact body.
    pub(super) fn begin_open(
        &self,
        resource: ResourceClause,
        source_index: usize,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.body.begin_open(resource, source_index)
    }

    /// Opens one proposition subproof at the current scope body's frontier.
    ///
    /// The returned scope is rooted at this scope's current checked body. It
    /// can only be incorporated back through `join_nested`, which verifies
    /// that exact ancestry before advancing the outer scope.
    pub(super) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        self.body.begin_have(proposition)
    }

    /// Incorporates one completed proposition or resource scope rooted at the
    /// current body as the outer scope's next checked structural node.
    ///
    /// This is the scope analogue of `Proof::apply_step`: callers cannot
    /// replace the body with an unrelated checked proof or skip intervening
    /// nodes. The nested join owns its exact `Have` certificate and exposes
    /// only that operation's output-sized fact delta to the outer scope.
    pub(super) fn join_nested(&self, nested: ProofScope<'a>) -> Result<Self, ClickError> {
        if !Arc::ptr_eq(&nested.root.context, &self.body.context)
            || !Arc::ptr_eq(&nested.root.state, &self.body.state)
            || !Arc::ptr_eq(&nested.root.node, &self.body.node)
        {
            return Err(self
                .root
                .step_error("nested proof scope is not rooted at the current scope body"));
        }
        // A nested resource may contain the terminal structural-effect frame.
        // Close its representation without retiring that sealed frontier;
        // only the outermost resource join owns final discharge.
        let body = nested.join_inner(false)?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("nested proof scope produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self
                .root
                .step_error("nested proof scope did not produce one direct checked successor"));
        }
        let mut next = self.clone();
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Applies one ordinary checked step inside the nested body. Failed
    /// candidates leave the enclosing scope value unchanged.
    pub(super) fn apply_step(&self, step: SimpleProofStep) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step_with_origin_mode(
            step,
            None,
            matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }),
        )?;
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Opens the C branch at this scope body's frontier as an in-`Proof`
    /// sibling split. The returned proof advances by focusing each recorded
    /// arm; `join_execution_split` accepts the direct joined successor.
    pub(super) fn split_execution_branch(
        &self,
    ) -> Result<(Proof<'a>, ExecutionSplit<'a>), ClickError> {
        self.body.split_focused_execution_branch()
    }

    /// Joins an advanced in-`Proof` execution split as the next direct
    /// structural node of this scope. The split's marker identity prevents
    /// a region searched from a sibling scope from being spliced here, and
    /// only the audited join's output-sized fact delta is exposed.
    pub(super) fn join_execution_split(
        &self,
        advanced: &Proof<'a>,
        record: &ExecutionSplit<'a>,
        empty: bool,
        ensuring: Option<Vec<ProofAssertion>>,
    ) -> Result<Self, ClickError> {
        let body = advanced.join_focused_execution_split(record, empty, ensuring)?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("execution branch join produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self
                .root
                .step_error("execution branch join did not produce one direct checked successor"));
        }
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Applies an already-expanded logical C branch inside this resource
    /// scope without constructing or comparing a parallel certificate.
    pub(super) fn apply_expanded_execution_if(
        &self,
        condition: &ClickProposition,
        then_steps: &[SimpleProofStep],
        else_steps: &[SimpleProofStep],
    ) -> Result<Self, ClickError> {
        let body = self
            .body
            .apply_expanded_execution_if(condition, then_steps, else_steps)?;
        let Some(parent) = body.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("expanded execution branch produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &self.body.node) {
            return Err(self.root.step_error(
                "expanded execution branch did not produce one direct checked successor",
            ));
        }
        #[cfg(test)]
        CHECKED_EXPANDED_EXECUTION_IFS.with(|count| count.set(count.get() + 1));
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(next)
    }

    pub(super) fn checkpoint(&self) -> ProofCheckpoint<'a> {
        self.body.checkpoint()
    }

    pub(super) fn certificate_since(
        &self,
        checkpoint: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        self.body.certificate_since(checkpoint)
    }

    /// Applies an already-expanded branch-shaped contextual frame through the
    /// same typed outcome-partition plan used by smart frame search. The
    /// source driver supplies only Surface operations; no certificate is
    /// constructed or interpreted at this compatibility boundary.
    pub(super) fn apply_contextual_frame_tactics_at(
        &self,
        condition: ClickProposition,
        then_tactics: Vec<ProofTactic>,
        else_tactics: Vec<ProofTactic>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let Ok(then_leaf) = ContextualFrameLeafPlan::from_surface_tactics(then_tactics) else {
            return Ok(None);
        };
        let Ok(else_leaf) = ContextualFrameLeafPlan::from_surface_tactics(else_tactics) else {
            return Ok(None);
        };
        let plan = ContextualFramePlan::If {
            condition,
            then_plan: Box::new(ContextualFramePlan::Leaf(then_leaf)),
            else_plan: Box::new(ContextualFramePlan::Leaf(else_leaf)),
        };
        let body = self.body.apply_contextual_frame_plan(
            &plan,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )?;
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Applies a source-owned simple step inside the scope. Terminal steps use
    /// the site only to schedule already-checked ordered outcome work.
    pub(super) fn apply_step_at(
        &self,
        step: SimpleProofStep,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step_with_origin_mode(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
            matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }),
        )?;
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(next)
    }

    /// Checks one proof-level `if` within a loop-effect resource-scope tree.
    /// The callbacks must retire their selected sibling goal, either by
    /// closing a terminal leaf or by recursively joining another `if`. This
    /// operation owns the split and structured join; the source driver only
    /// selects the two already-lowered arm certificates.
    pub(super) fn apply_loop_effect_if<Then, Else>(
        scopes: &[Self],
        current: Self,
        condition: ClickProposition,
        apply_then: Then,
        apply_else: Else,
    ) -> Result<Proof<'a>, ClickError>
    where
        Then: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
        Else: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
    {
        Self::validate_loop_effect_open_scopes(scopes)?;
        let inner = scopes
            .last()
            .expect("the nonempty leading scope chain has an inner scope");
        if !Arc::ptr_eq(&current.root.context, &inner.root.context)
            || !Arc::ptr_eq(&current.root.state, &inner.root.state)
            || !Arc::ptr_eq(&current.root.node, &inner.root.node)
        {
            return Err(inner
                .root
                .step_error("loop-effect branch cursor left its innermost open scope"));
        }
        let mut then_scope = current.clone();
        let mut else_scope = current.clone();
        current.body.apply_execution_if_with(
            condition,
            |then_body| {
                then_scope.body = then_body;
                apply_then(then_scope)
            },
            |else_body| {
                else_scope.body = else_body;
                apply_else(else_scope)
            },
        )
    }

    /// Checks one logical `cases` scope within a loop-effect resource tree.
    /// Each callback owns exactly one disjunct sibling; resource
    /// representations close independently before the audited logical join.
    pub(super) fn apply_loop_effect_cases<Left, Right>(
        scopes: &[Self],
        current: Self,
        disjunction: ClickProposition,
        apply_left: Left,
        apply_right: Right,
    ) -> Result<Proof<'a>, ClickError>
    where
        Left: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
        Right: FnOnce(Self) -> Result<Proof<'a>, ClickError>,
    {
        Self::validate_loop_effect_open_scopes(scopes)?;
        let inner = scopes
            .last()
            .expect("the nonempty leading scope chain has an inner scope");
        if !Arc::ptr_eq(&current.root.context, &inner.root.context)
            || !Arc::ptr_eq(&current.root.state, &inner.root.state)
            || !Arc::ptr_eq(&current.root.node, &inner.root.node)
        {
            return Err(inner
                .root
                .step_error("loop-effect cases cursor left its innermost open scope"));
        }
        let mut left_scope = current.clone();
        let mut right_scope = current.clone();
        current.body.apply_execution_cases_with(
            disjunction,
            |left_body| {
                left_scope.body = left_body;
                apply_left(left_scope)
            },
            |right_body| {
                right_scope.body = right_body;
                apply_right(right_scope)
            },
        )
    }

    /// Closes every currently open resource representation on one terminal
    /// branch, then retires that leaf goal. No surface step is synthesized:
    /// the leaf operations and later audited `if` joins retain the exact
    /// provenance, while resource closure is the semantics of the enclosing
    /// `open` nodes.
    pub(super) fn complete_loop_effect_leaf(
        scopes: &[Self],
        leaf: Self,
    ) -> Result<Proof<'a>, ClickError> {
        Self::validate_loop_effect_open_scopes(scopes)?;
        let inner = scopes
            .last()
            .expect("the nonempty leading scope chain has an inner scope");
        if !Arc::ptr_eq(&leaf.root.context, &inner.root.context)
            || !Arc::ptr_eq(&leaf.root.state, &inner.root.state)
            || !Arc::ptr_eq(&leaf.root.node, &inner.root.node)
        {
            return Err(inner
                .root
                .step_error("loop-effect leaf left its innermost open scope"));
        }
        let mut body = leaf.body;
        for scope in scopes.iter().rev() {
            body = scope.close_open_resource_on_focused_branch(body)?;
        }
        scopes[0].discharge_closed_loop_effect_branch(body)
    }

    /// Retains a checked branch subtree inside the open scopes introduced at
    /// `wrap_from`. Earlier scopes remain semantic ancestors and are wrapped
    /// by their own caller. Prefix operations before each nested `open` come
    /// from that child scope's checked root lineage, so serialization loses
    /// neither scope-local work nor branch structure.
    pub(super) fn retain_loop_effect_open_scopes(
        scopes: &[Self],
        wrap_from: usize,
        joined: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        Self::validate_loop_effect_open_scopes(scopes)?;
        if wrap_from > scopes.len() {
            return Err(scopes[0]
                .root
                .step_error("loop-effect open-scope provenance boundary is out of range"));
        }
        if wrap_from == scopes.len() {
            return Ok(joined);
        }

        let mut body = joined.certificate();
        for index in ((wrap_from + 1)..scopes.len()).rev() {
            let scope = &scopes[index];
            let ProofScopeStructure::Open { resource, .. } = scope.structure.as_ref() else {
                unreachable!("the scope kinds were checked above")
            };
            let mut steps = scope.root.certificate().steps().to_vec();
            steps.push(SimpleProofStep::Open {
                resource: resource.clone(),
                proof: Box::new(body),
            });
            body = ProofCertificate::from_steps(steps);
        }
        let outer = &scopes[wrap_from];
        let ProofScopeStructure::Open { resource, .. } = outer.structure.as_ref() else {
            unreachable!("the scope kind was checked above")
        };
        let mut introduced_facts = PersistentOrderedSet::default();
        for scope in &scopes[wrap_from..] {
            for fact in &scope.introduced_facts {
                introduced_facts.insert(fact.clone());
            }
        }
        let introduced_facts = introduced_facts.to_vec();
        let mut state = Arc::unwrap_or_clone(joined.state.clone());
        state.added_facts = Arc::new(introduced_facts.clone());
        state.checked_facts = Arc::new(introduced_facts);
        Ok(Proof {
            context: outer.root.context.clone(),
            state: Arc::new(state),
            node: Arc::new(ProofNode {
                parent: Some(outer.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::Open {
                    resource: resource.clone(),
                    proof: Box::new(body),
                })),
                focused: outer.root.focused,
                depth: outer.root.node.depth + 1,
            }),
            focused: outer.root.focused,
        })
    }

    fn validate_loop_effect_open_scopes(scopes: &[Self]) -> Result<(), ClickError> {
        let Some(outer) = scopes.first() else {
            return Err(ClickError::new(
                "a loop-effect branch requires at least one open resource scope",
            ));
        };
        if scopes
            .iter()
            .any(|scope| !matches!(scope.structure.as_ref(), ProofScopeStructure::Open { .. }))
        {
            return Err(outer
                .root
                .step_error("a loop-effect branch requires open resource scopes"));
        }
        for pair in scopes.windows(2) {
            let [parent, child] = pair else {
                unreachable!("a two-element scope window has two entries")
            };
            if !Arc::ptr_eq(&child.root.context, &parent.body.context)
                || !Arc::ptr_eq(&child.root.state, &parent.body.state)
                || !Arc::ptr_eq(&child.root.node, &parent.body.node)
            {
                return Err(outer
                    .root
                    .step_error("leading open scopes do not form one checked Proof chain"));
            }
        }
        Ok(())
    }

    /// Closes this open resource on the currently focused terminal branch
    /// without yet retiring the branch goal. This is the per-arm half of
    /// a recursive loop-effect branch tree; logical joins are allowed only after
    /// both independently checked representations have closed.
    fn close_open_resource_on_focused_branch(
        &self,
        body: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        let ProofScopeStructure::Open {
            resource,
            source_index,
            preserve_exposed_body,
        } = self.structure.as_ref()
        else {
            unreachable!("only an open scope closes a resource representation")
        };
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("an open scope can only be created from an execution Proof")
        };
        if !body.focused_loop_effect_closed() {
            return Err(self.root.step_error(
                "cannot close an open resource branch before its loop-effect goal is proved",
            ));
        }
        let mut execution = body
            .goal_execution()
            .cloned()
            .map(Arc::unwrap_or_clone)
            .ok_or_else(|| {
                self.root
                    .step_error("open resource branch lost its execution frontier")
            })?;
        let mut facts = body.facts().clone();
        execution.replay.open_scopes = execution.replay.open_scopes.saturating_sub(1);
        if execution.replay.is_at_function_exit() {
            execution.replay.defer_post_execution(
                context.tactic_index,
                *source_index,
                PostExecutionTactic::CloseOpen {
                    resource: resource.clone(),
                    preserve_exposed_body: *preserve_exposed_body,
                },
            );
        } else {
            let pre_state = execution
                .replay
                .old_reference_state(&execution.state)
                .clone();
            let checked = close_open_resource_for_proof(
                context.resource_environment,
                resource,
                context.claim_label,
                context.tactic_index,
                facts,
                context.parsed_function.parameters(),
                context.arguments,
                &pre_state,
                execution.state.into_value(),
                context.predicate_environment,
                context.click_function_environment,
                &execution.replay.unfolded_predicates,
                *preserve_exposed_body,
            )?;
            facts = checked.facts;
            execution.state = checked.state.into();
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let mut state = Arc::unwrap_or_clone(body.state.clone());
        state.goals = state
            .goals
            .replace_frontier_at(body.focused, facts, execution);
        Ok(Proof {
            context: body.context.clone(),
            state: Arc::new(state),
            node: Arc::new(ProofNode {
                parent: Some(body.node.clone()),
                step: None,
                focused: body.focused,
                depth: body.node.depth,
            }),
            focused: body.focused,
        })
    }

    /// Retires one sealed effect arm only after its resource representation
    /// has closed. The marker carries no surface step: closure and discharge
    /// are the audited exit semantics of the enclosing `open` and `if`.
    fn discharge_closed_loop_effect_branch(
        &self,
        body: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        if !body.focused_loop_effect_closed() {
            return Err(self
                .root
                .step_error("cannot discharge an unfinished loop-effect branch"));
        }
        let mut state = Arc::unwrap_or_clone(body.state.clone());
        state.goals = state.goals.discharge_at(body.focused);
        Ok(Proof {
            context: body.context.clone(),
            state: Arc::new(state),
            node: Arc::new(ProofNode {
                parent: Some(body.node.clone()),
                step: None,
                focused: body.focused,
                depth: body.node.depth,
            }),
            focused: body.focused,
        })
    }

    /// Reports whether a terminal frame step can use the checked Proof-owned
    /// operation. Unsupported forms leave this scope untouched so a larger
    /// transactional Proof attempt can decline without observing a partial
    /// transition.
    pub(super) fn supports_checked_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        self.body
            .supports_checked_execution_frame_using(region, premises)
    }

    /// Searches for a frame certificate and submits the selected candidate to
    /// the owned Proof exactly once. The cheap exact-empty candidate goes
    /// first; a miss invokes contextual derivation search, which may add
    /// explicit checked `have` steps before the terminal `FrameUsing`.
    pub(super) fn try_smart_frame_at(
        &self,
        region: Option<&CodeRegionRef>,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Option<Self>, ClickError> {
        let checkpoint = self.body.checkpoint();
        let Some(body) = self
            .body
            .try_smart_frame_at(region, tactic_index, source_index)?
        else {
            return Ok(None);
        };
        let candidate = body.certificate_since(&checkpoint)?;
        let mut next = self.clone();
        for step in candidate.steps() {
            if let SimpleProofStep::Have { proposition, .. } = step {
                let fact = body.lower_surface_proposition(
                    proposition,
                    "smart frame intermediate proposition",
                )?;
                if !next.introduced_facts.contains(&fact) {
                    next.introduced_facts.push(fact);
                }
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the narrow linear `execute` search inside this scope.
    ///
    /// Each selected statement is checked and retained by
    /// `Proof::try_indexed_statement_step`; the search never mutates a second
    /// semantic context or reconstructs steps from its aftermath. A partial
    /// advance is discarded unless the checked descendant reaches function
    /// exit, so unsupported frontiers continue through the legacy path.
    pub(super) fn try_linear_execute(&self) -> Result<Option<Self>, ClickError> {
        let Some((body, added_facts)) = self.body.try_linear_execute_descendant()? else {
            return Ok(None);
        };
        let mut introduced_facts = self.introduced_facts.clone();
        for fact in added_facts {
            if !introduced_facts.contains(&fact) {
                introduced_facts.push(fact);
            }
        }
        let mut next = self.clone();
        next.introduced_facts = introduced_facts;
        next.body = body;
        Ok(Some(next))
    }

    /// Selects and applies one smart statement step on the scope's checked
    /// child Proof. The accepted descendant, including its exact `StepUsing`
    /// certificate and fact delta, becomes the next scope body directly.
    pub(super) fn try_smart_step(&self) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_indexed_execute_step()? else {
            return Ok(None);
        };
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs bare theorem-application search on the scope's current checked
    /// body and retains only the accepted explicit theorem step. Function-exit
    /// applications remain outcome-local ordered-finalization operations.
    pub(super) fn try_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<Option<Self>, ClickError> {
        if self.body.is_at_function_exit() {
            return Ok(None);
        }
        let Some(body) = self.body.try_theorem_application(application)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        if matches!(self.structure.as_ref(), ProofScopeStructure::Open { .. }) {
            for fact in body.added_facts() {
                if !next.introduced_facts.contains(fact) {
                    next.introduced_facts.push(fact.clone());
                }
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs bare fact-transport search on the scope's current checked body.
    /// Failed candidate descendants are discarded by `Proof`; the enclosing
    /// scope receives only the successful retained `TransportUsing` node.
    pub(super) fn try_fact_transport(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        if self.body.is_at_function_exit() {
            return Ok(None);
        }
        let Some(body) = self.body.try_execution_fact_transport(source, target)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        for fact in body.added_facts() {
            if !next.introduced_facts.contains(fact) {
                next.introduced_facts.push(fact.clone());
            }
        }
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the narrow straight-line `execute_until` search on checked
    /// descendants and stops before the selected source statement.
    pub(super) fn try_linear_execute_until(
        &self,
        region: &CodeRegionRef,
    ) -> Result<Option<Self>, ClickError> {
        let Some((body, added_facts)) = self.body.try_linear_execute_until_descendant(region)?
        else {
            return Ok(None);
        };
        let mut introduced_facts = self.introduced_facts.clone();
        for fact in added_facts {
            if !introduced_facts.contains(&fact) {
                introduced_facts.push(fact);
            }
        }
        let mut next = self.clone();
        next.introduced_facts = introduced_facts;
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the small shared smart closure search inside the nested proof.
    /// Every accepted candidate still advances through `Proof::apply_step`.
    pub(super) fn try_direct_logical_closure(&self) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_direct_logical_closure()? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Runs the migrated `simp` search inside the nested proof and retains
    /// the accepted descendant directly.
    pub(super) fn try_simp_closure(&self) -> Result<Option<Self>, ClickError> {
        let Some(mut body) = self.body.try_simp_closure()? else {
            return Ok(None);
        };
        if body.node.depth == 1
            && matches!(body.node.step.as_deref(), Some(SimpleProofStep::Assumption))
            && let Some(replayable) = self.body.try_simp_closure_after_direct(true)?
        {
            body = replayable;
        }
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Runs one supported source script inside the owned nested body and
    /// retains its already-checked descendant.
    pub(super) fn try_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_linear_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Checks a source body after its enclosing driver has selected Proof as
    /// the authority for this scope. Explicit failures remain checked errors
    /// through every nested scope and logical arm.
    pub(super) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_authoritative_linear_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Applies a planner-selected recursive script inside this owned scope,
    /// retaining the checked body descendant without materializing a
    /// certificate.
    pub(super) fn try_planned_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_planned_linear_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Smart-only compatibility wrapper retained for focused regressions.
    #[cfg(test)]
    pub(super) fn try_linear_smart_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(body) = self.body.try_linear_smart_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Closes a completed nested proof and makes its checked proposition
    /// available in the enclosing proof while retaining the exact body.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
        self.join_inner(true)
    }

    /// Joins one scope, optionally retiring a sealed structural-effect goal.
    /// Nested resource joins pass `false` so all enclosing resource
    /// representations close before the outermost join discharges the goal.
    fn join_inner(self, discharge_closed_loop_effect: bool) -> Result<Proof<'a>, ClickError> {
        match *self.structure {
            ProofScopeStructure::Have {
                proposition,
                kernel,
            } => {
                if !self.body.is_complete() {
                    return Err(self
                        .root
                        .step_error("cannot close `have`: nested proof is incomplete"));
                }
                let body = self.body.certificate();
                let mut facts = self.root.facts().clone();
                facts = facts.with_fact(kernel.clone());
                let mut goals = self
                    .root
                    .state
                    .goals
                    .with_facts_at(self.root.focused, facts);
                if let Some(Goal::FunctionOutcome(outcome)) = goals.get(self.root.focused).cloned()
                {
                    let mut updated = outcome;
                    let mut point = (*updated.point).clone();
                    point
                        .surface_propositions
                        .record_lowering(&proposition, &kernel)?;
                    updated.point = Arc::new(point);
                    goals = goals.replace_at(self.root.focused, Goal::FunctionOutcome(updated));
                }
                Ok(Proof {
                    context: self.root.context.clone(),
                    state: Arc::new(ProofState {
                        locals: self.root.state.locals.clone(),
                        goals,
                        added_facts: Arc::new(vec![kernel.clone()]),
                        checked_facts: Arc::new(vec![kernel]),
                    }),
                    node: Arc::new(ProofNode {
                        parent: Some(self.root.node.clone()),
                        step: Some(Arc::new(SimpleProofStep::Have {
                            proposition,
                            proof: Box::new(body),
                        })),
                        focused: self.root.focused,
                        depth: self.root.node.depth + 1,
                    }),
                    focused: self.root.focused,
                })
            }
            ProofScopeStructure::Open {
                resource,
                source_index,
                preserve_exposed_body,
            } => {
                let ProofContext::Execution(context) = self.root.context.as_ref() else {
                    unreachable!("an open scope can only be created from an execution Proof")
                };
                let body = self.body.certificate();
                let loop_effect_closed = self.body.focused_loop_effect_closed();
                let mut execution = self
                    .body
                    .goal_execution()
                    .cloned()
                    .map(Arc::unwrap_or_clone)
                    .ok_or_else(|| {
                        self.root
                            .step_error("open scope body lost its execution frontier")
                    })?;
                let mut facts = self.body.facts().clone();
                let mut state = Arc::unwrap_or_clone(self.body.state);
                execution.replay.open_scopes = execution.replay.open_scopes.saturating_sub(1);
                if execution.replay.is_at_function_exit() {
                    execution.replay.defer_post_execution(
                        context.tactic_index,
                        source_index,
                        PostExecutionTactic::CloseOpen {
                            resource: resource.clone(),
                            preserve_exposed_body,
                        },
                    );
                } else {
                    let pre_state = execution
                        .replay
                        .old_reference_state(&execution.state)
                        .clone();
                    let checked = close_open_resource_for_proof(
                        context.resource_environment,
                        &resource,
                        context.claim_label,
                        context.tactic_index,
                        facts,
                        context.parsed_function.parameters(),
                        context.arguments,
                        &pre_state,
                        execution.state.into_value(),
                        context.predicate_environment,
                        context.click_function_environment,
                        &execution.replay.unfolded_predicates,
                        preserve_exposed_body,
                    )?;
                    facts = checked.facts;
                    execution.state = checked.state.into();
                }
                execution.last_step_delta = ExecutionProofStepDelta::default();
                state.goals = state
                    .goals
                    .replace_frontier_at(self.body.focused, facts, execution);
                if discharge_closed_loop_effect && loop_effect_closed {
                    state.goals = state.goals.discharge_at(self.body.focused);
                }
                state.added_facts = Arc::new(self.introduced_facts.clone());
                state.checked_facts = Arc::new(self.introduced_facts);
                // The successor's goal map came from the scope body, whose
                // cursor may have moved through a decided branch.
                let focused = self.body.focused;
                Ok(Proof {
                    context: self.root.context.clone(),
                    state: Arc::new(state),
                    node: Arc::new(ProofNode {
                        parent: Some(self.root.node.clone()),
                        step: Some(Arc::new(SimpleProofStep::Open {
                            resource,
                            proof: Box::new(body),
                        })),
                        focused,
                        depth: self.root.node.depth + 1,
                    }),
                    focused,
                })
            }
        }
    }
}

impl ProofContext<'_> {
    fn claim_label(&self) -> &str {
        match self {
            Self::Pure(context) => context.claim_label,
            Self::Point(context) => context.claim_label,
            Self::Execution(context) => context.claim_label,
        }
    }
}

impl ProofFacts {
    pub(super) fn from_ordered(facts: &[Proposition]) -> Self {
        let mut ordered = PersistentSequence::default();
        let mut top_level_exact = PersistentSet::default();
        let mut exact = PersistentSet::default();
        let mut proper_conjuncts = PersistentSet::default();
        let mut by_snapshot_blind = PersistentMap::default();
        let mut bitvector_equalities_by_atom = PersistentMap::default();
        let mut by_quantified_replay = PersistentMap::default();
        let mut memory_effect_summaries = PersistentSequence::default();
        let mut implications_by_consequent = PersistentMap::default();
        let mut assumptions = PureFactContext::new();
        let mut implicit_transport_assumptions = PureFactContext::new();
        let mut by_predicate = PersistentMap::default();
        for fact in facts {
            if top_level_exact.contains(fact) {
                continue;
            }
            ordered.push(fact.clone());
            top_level_exact = top_level_exact.with_value(fact.clone());
            by_quantified_replay = index_quantified_replay_fact(by_quantified_replay, fact);
            if matches!(fact, Proposition::CMemoryEffectSummary { .. }) {
                memory_effect_summaries.push(fact.clone());
            }
            implications_by_consequent =
                index_implication_consequents(implications_by_consequent, fact);
            by_predicate = index_predicate_fact(by_predicate, fact);
            if matches!(fact, Proposition::And(_, _)) {
                proper_conjuncts = index_proper_conjuncts(proper_conjuncts, fact);
                let mut conjuncts = Vec::new();
                collect_owned_atomic_conjuncts(fact, &mut conjuncts);
                for conjunct in conjuncts {
                    by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                    bitvector_equalities_by_atom =
                        index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                    exact = exact.with_value(conjunct);
                }
            }
            by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, fact);
            bitvector_equalities_by_atom =
                index_bitvector_equality_fact(bitvector_equalities_by_atom, fact);
            exact = exact.with_value(fact.clone());
            assumptions = assumptions.assume_proposition(fact.clone());
            implicit_transport_assumptions =
                index_implicit_transport_context(implicit_transport_assumptions, fact);
        }
        Self {
            ordered,
            prioritized: None,
            top_level_exact,
            exact,
            proper_conjuncts,
            by_snapshot_blind,
            bitvector_equalities_by_atom,
            by_quantified_replay,
            memory_effect_summaries,
            predicate_unfolded_universal_facts: PersistentSequence::default(),
            implications_by_consequent,
            assumptions,
            implicit_transport_assumptions,
            by_predicate,
        }
    }

    /// Rebuilds a legacy drain view while retaining the exact provenance
    /// indexes owned by facts that remain available. The adapter iterates
    /// only the explicit predicate-unfold delta, never the ambient fact set.
    fn resync_ordered_preserving_provenance(&self, facts: &[Proposition]) -> Self {
        let mut successor = Self::from_ordered(facts);
        for fact in self.predicate_unfolded_universal_facts.iter() {
            if successor.contains_top_level(fact) {
                successor = successor.with_predicate_unfold_fact(fact.clone());
            }
        }
        successor
    }

    pub(in crate::lang::click::proof) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
    }

    pub(super) fn contains_top_level(&self, fact: &Proposition) -> bool {
        self.top_level_exact.contains(fact)
    }

    pub(super) fn with_fact(&self, fact: Proposition) -> Self {
        if self.top_level_exact.contains(&fact) {
            return self.clone();
        }
        let mut exact = self.exact.clone();
        let mut proper_conjuncts = self.proper_conjuncts.clone();
        let mut by_snapshot_blind = self.by_snapshot_blind.clone();
        let mut bitvector_equalities_by_atom = self.bitvector_equalities_by_atom.clone();
        let by_quantified_replay =
            index_quantified_replay_fact(self.by_quantified_replay.clone(), &fact);
        let mut memory_effect_summaries = self.memory_effect_summaries.clone();
        if matches!(fact, Proposition::CMemoryEffectSummary { .. }) {
            memory_effect_summaries.push(fact.clone());
        }
        let implications_by_consequent =
            index_implication_consequents(self.implications_by_consequent.clone(), &fact);
        if matches!(fact, Proposition::And(_, _)) {
            proper_conjuncts = index_proper_conjuncts(proper_conjuncts, &fact);
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                bitvector_equalities_by_atom =
                    index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                exact = exact.with_value(conjunct);
            }
        }
        by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &fact);
        bitvector_equalities_by_atom =
            index_bitvector_equality_fact(bitvector_equalities_by_atom, &fact);
        exact = exact.with_value(fact.clone());
        let mut ordered = self.ordered.clone();
        ordered.push(fact.clone());
        let implicit_transport_assumptions =
            index_implicit_transport_context(self.implicit_transport_assumptions.clone(), &fact);
        Self {
            ordered,
            prioritized: self.prioritized.clone(),
            top_level_exact: self.top_level_exact.with_value(fact.clone()),
            exact,
            proper_conjuncts,
            by_snapshot_blind,
            bitvector_equalities_by_atom,
            by_quantified_replay,
            memory_effect_summaries,
            predicate_unfolded_universal_facts: self.predicate_unfolded_universal_facts.clone(),
            implications_by_consequent,
            assumptions: self.assumptions.clone().assume_proposition(fact.clone()),
            implicit_transport_assumptions,
            by_predicate: index_predicate_fact(self.by_predicate.clone(), &fact),
        }
    }

    pub(super) fn with_predicate_unfold_fact(&self, fact: Proposition) -> Self {
        let is_universal = matches!(fact, Proposition::ForAll { .. });
        let mut successor = self.with_fact(fact.clone());
        if is_universal
            && !successor
                .predicate_unfolded_universal_facts
                .iter()
                .any(|candidate| candidate == &fact)
        {
            successor.predicate_unfolded_universal_facts.push(fact);
        }
        successor
    }

    /// Materializes one selected separation from the compact resource-
    /// composition index. This is target-driven: unrelated resource pairs
    /// remain implicit, while a successful result is an exact fact for the
    /// ordinary `Assumption` checker in the new point goal.
    fn with_selected_resource_separation(&self, goal: &Proposition) -> Self {
        if matches!(
            goal,
            Proposition::CResourceSeparate { .. } | Proposition::CMemoryDisjoint { .. }
        ) && !self.contains(goal)
            && self.assumptions.proves(goal)
        {
            self.with_fact(goal.clone())
        } else {
            self.clone()
        }
    }

    /// Materializes one selected equality across a checked chain of load
    /// variables. This keeps the ordinary `Assumption` checker exact while
    /// allowing a new point goal to consume equality transport explicitly
    /// carried through the preceding statement. Selection follows only the
    /// goal's indexed equality buckets; unrelated ambient equalities remain
    /// implicit and are never visited.
    fn with_selected_load_equality_bridge(&self, goal: &Proposition) -> Self {
        if self.pure_replay_available(goal)
            || !matches!(
                goal,
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
            )
        {
            return self.clone();
        }
        let candidates = self.bitvector_equalities_mentioning(goal);
        if !candidates.is_empty()
            && premise_bridged_by_load_variable_chain_with_origins(
                goal,
                &candidates,
                &self.assumptions,
            )
        {
            self.with_fact(goal.clone())
        } else {
            self.clone()
        }
    }

    pub(super) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    fn memory_effect_summaries(&self) -> impl Iterator<Item = &Proposition> {
        self.memory_effect_summaries.iter()
    }

    /// Exact proper-conjunct membership with the same condition-polarity
    /// equivalence as the legacy structural checker.
    pub(super) fn contains_proper_conjunct(&self, required: &Proposition) -> bool {
        self.proper_conjuncts.contains(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.proper_conjuncts.contains(form))
    }

    /// Exact or direct-load-materialization-equivalent availability used by
    /// the deterministic rewrite rule. Unlike snapshot replay, this does not
    /// admit polarity changes or a semantic bridge beyond normalization.
    pub(super) fn materialization_available(&self, required: &Proposition) -> bool {
        self.exact.contains(required)
    }

    /// Availability of a proposition to the explicit pure `assumption`
    /// judgment used inside point proofs. This deliberately excludes
    /// cross-effect snapshot transport: such a transport needs its own
    /// retained simple step before a later assumption may consume it.
    pub(super) fn pure_replay_available(&self, required: &Proposition) -> bool {
        self.materialization_available(required) || self.quantified_replay_available(required)
    }

    pub(super) fn implicit_transport_assumptions(&self) -> &PureFactContext {
        &self.implicit_transport_assumptions
    }

    /// Adds one statement's selected successor context while retaining the
    /// old ambient order by shared prefix. The statement delta is explicit,
    /// so insertion work is proportional only to that delta and index height.
    pub(super) fn with_statement_facts(&self, facts: Vec<Proposition>) -> Self {
        let ordered = self.ordered.clone();
        let parent = self.prioritized.clone();
        let mut successor = self.clone();
        for fact in &facts {
            successor = successor.with_fact(fact.clone());
        }
        successor.ordered = ordered;
        successor.prioritized = Some(Arc::new(PrioritizedProofFacts {
            parent,
            facts: Arc::new(facts),
        }));
        successor
    }

    /// Availability accepted by explicit replay, answered from persistent
    /// indexes. Snapshot-blind buckets only select structurally compatible
    /// candidates; the kernel still proves every cross-snapshot match.
    pub(super) fn replay_available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.exact_available_across_effects(required, framing) {
            return true;
        }

        self.quantified_replay_available(required)
    }

    /// Returns one actual available fact accepted by explicit replay. Smart
    /// syntax selection needs the retained fact, not merely a yes/no answer:
    /// its recorded surface form may carry a statement snapshot that the
    /// freshly lowered theorem requirement no longer exposes.
    fn matching_replay_fact_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> Option<Proposition> {
        let keys = [snapshot_blind_proposition_key(required)];
        let mut indexed_candidates = Vec::new();
        for key in &keys {
            if let Some(bucket) = self.by_snapshot_blind.get(key) {
                for candidate in bucket.iter() {
                    if !indexed_candidates.contains(candidate) {
                        indexed_candidates.push(candidate.clone());
                    }
                }
            }
        }
        // Preserve the legacy selector's canonical materialization choice,
        // but search only the requirement's persistent shape bucket. The
        // chosen sibling snapshot can have a stable recorded `at(...)`
        // form even when the freshly lowered requirement is also present.
        if let Some(candidate) = exactly_available_fact(required, &indexed_candidates) {
            return Some(candidate.clone());
        }
        if self.exact.contains(required) {
            return Some(required.clone());
        }
        if let Some(form) = condition_polarity_forms(required)
            .into_iter()
            .find(|form| self.exact.contains(form))
        {
            return Some(form);
        }

        if let Some(quantified) = self.matching_quantified_replay_fact(required) {
            return Some(quantified);
        }

        let mut candidates = Vec::new();
        for key in keys {
            let Some(bucket) = self.by_snapshot_blind.get(&key) else {
                continue;
            };
            for candidate in bucket.iter() {
                if !candidates.contains(candidate) {
                    candidates.push(candidate.clone());
                }
                if candidate == required
                    || separation_bridged_fact_is_available(
                        required,
                        std::slice::from_ref(candidate),
                        &self.assumptions,
                        framing,
                    )
                {
                    return Some(candidate.clone());
                }
            }
        }
        separation_bridged_fact_is_available(required, &candidates, &self.assumptions, framing)
            .then(|| required.clone())
    }

    fn matching_quantified_replay_fact(&self, required: &Proposition) -> Option<Proposition> {
        self.matching_quantified_replay_facts(required)
            .into_iter()
            .next()
    }

    fn matching_quantified_replay_facts(&self, required: &Proposition) -> Vec<Proposition> {
        quantified_replay_index_key(required)
            .and_then(|key| self.by_quantified_replay.get(&key))
            .into_iter()
            .flat_map(PersistentSequence::iter)
            .filter(|candidate| {
                quantified_binder_equivalent(required, candidate)
                    || quantified_replay_equivalent_available_fact(
                        required,
                        std::slice::from_ref(candidate),
                    )
                    .is_some()
            })
            .cloned()
            .collect()
    }

    fn quantified_replay_available(&self, required: &Proposition) -> bool {
        self.matching_quantified_replay_fact(required).is_some()
    }

    fn contains_discharged_implication_consequent(&self, required: &Proposition) -> bool {
        let keys = vec![snapshot_blind_proposition_key(required)];
        keys.into_iter()
            .filter_map(|key| self.implications_by_consequent.get(&key))
            .flat_map(PersistentSequence::iter)
            .any(|candidate| {
                &candidate.consequent == required
                    && candidate
                        .antecedents
                        .iter()
                        .all(|antecedent| self.replay_available_across_effects(antecedent, &[]))
            })
    }

    pub(super) fn exact_available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.contains(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.exact.contains(form))
        {
            return true;
        }

        let keys = [snapshot_blind_proposition_key(required)];
        let mut candidates = Vec::new();
        for key in keys {
            if let Some(bucket) = self.by_snapshot_blind.get(&key) {
                for candidate in bucket.iter() {
                    if !candidates.contains(candidate) {
                        candidates.push(candidate.clone());
                    }
                }
            }
        }
        if candidates.is_empty() {
            return false;
        }
        separation_bridged_fact_is_available(required, &candidates, &self.assumptions, framing)
    }

    pub(super) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        directly_conflicts_with_normalized_index(&self.exact, fact)
    }

    /// Returns exact equality facts attached to terms occurring in this
    /// proposition. Selection cost follows the proposition and the matching
    /// equality buckets; unrelated ambient equalities are never visited.
    fn bitvector_equalities_mentioning(&self, proposition: &Proposition) -> Vec<Proposition> {
        let mut atoms = BTreeSet::new();
        collect_proposition_bitvector_atoms(proposition, &mut atoms);
        let mut equalities = Vec::new();
        for atom in atoms {
            if let Some(bucket) = self.bitvector_equalities_by_atom.get(&atom) {
                for equality in bucket.iter() {
                    equalities.push(equality.clone());
                }
            }
        }
        equalities
    }

    /// The facts this context introduced after `ancestor`, oldest first.
    ///
    /// Both fact stores are parent-linked and append-only, so the delta is
    /// recovered by walking only the appended suffixes — prioritized
    /// statement batches first, then ordinary insertions — and pointer
    /// identity proves the shared history. Returns `None` when `ancestor`
    /// is not this context's ancestor. This is the output-sensitive
    /// introduction delta the execution sibling-split joins consume.
    pub(super) fn introduced_since(&self, ancestor: &Self) -> Option<Vec<Proposition>> {
        let mut new_batches = Vec::new();
        let mut current = self.prioritized.clone();
        loop {
            match (&current, &ancestor.prioritized) {
                (Some(node), Some(ancestor_head)) if Arc::ptr_eq(node, ancestor_head) => break,
                (None, None) => break,
                (Some(node), _) => {
                    new_batches.push(node.facts.clone());
                    current = node.parent.clone();
                }
                (None, Some(_)) => return None,
            }
        }
        let ordered_suffix = self.ordered.suffix_since(&ancestor.ordered)?;
        let mut introduced = Vec::new();
        for batch in new_batches.iter().rev() {
            introduced.extend(batch.iter().cloned());
        }
        introduced.extend(ordered_suffix);
        Some(introduced)
    }

    pub(super) fn to_vec(&self) -> Vec<Proposition> {
        let mut ordered = Vec::new();
        let mut seen = BTreeSet::new();
        let mut batch = self.prioritized.as_deref();
        while let Some(current) = batch {
            for fact in current.facts.iter() {
                if seen.insert(fact.clone()) {
                    ordered.push(fact.clone());
                }
            }
            batch = current.parent.as_deref();
        }
        for fact in self.ordered.iter() {
            if seen.insert(fact.clone()) {
                ordered.push(fact.clone());
            }
        }
        ordered
    }

    pub(super) fn mentioning_predicate(&self, name: &String) -> impl Iterator<Item = &Proposition> {
        self.by_predicate
            .get(name)
            .into_iter()
            .flat_map(PersistentSequence::iter)
    }

    #[cfg(test)]
    fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.exact.lookup_comparisons(fact)
    }

    #[cfg(test)]
    fn equality_atom_lookup_comparisons(&self, term: &Bitvector32Term) -> usize {
        let key = bitvector_equality_atom_key(term).expect("test term should be an indexed atom");
        self.bitvector_equalities_by_atom.lookup_comparisons(&key)
    }
}

fn index_snapshot_fact(
    mut by_snapshot_blind: PersistentMap<
        SnapshotBlindPropositionKey,
        PersistentSequence<Proposition>,
    >,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>> {
    for key in [snapshot_blind_proposition_key(fact)] {
        if !key.forgets_a_snapshot() {
            continue;
        }
        let mut bucket = by_snapshot_blind.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            by_snapshot_blind = by_snapshot_blind.with_inserted(key, bucket);
        }
    }
    by_snapshot_blind
}

fn index_bitvector_equality_fact(
    mut index: PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Proposition>> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = fact else {
        return index;
    };
    for term in [left.as_ref(), right.as_ref()] {
        let Some(key) = bitvector_equality_atom_key(term) else {
            continue;
        };
        let mut bucket = index.get(&key).cloned().unwrap_or_default();
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

fn bitvector_equality_atom_key(term: &Bitvector32Term) -> Option<BitvectorEqualityAtomKey> {
    match term {
        Bitvector32Term::Constant(value) => Some(BitvectorEqualityAtomKey::Constant(*value)),
        Bitvector32Term::Variable(variable) => Some(BitvectorEqualityAtomKey::Variable(*variable)),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(pointer.as_ref(), &mut hasher);
            Some(BitvectorEqualityAtomKey::MemoryLoad {
                memory: memory.arena_id(),
                pointer_hash: std::hash::Hasher::finish(&hasher),
            })
        }
        _ => None,
    }
}

fn collect_proposition_bitvector_atoms(
    proposition: &Proposition,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match proposition {
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_atoms(condition, atoms)
        }
        Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. }
        | Proposition::Not(body) => collect_proposition_bitvector_atoms(body, atoms),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_atoms(left, atoms);
            collect_proposition_bitvector_atoms(right, atoms);
        }
        _ => {}
    }
}

fn collect_condition_bitvector_atoms(
    condition: &ConditionTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(&left.offset, atoms);
            collect_pointer_offset_bitvector_atoms(&right.offset, atoms);
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
    }
}

fn collect_bitvector_atoms(term: &Bitvector32Term, atoms: &mut BTreeSet<BitvectorEqualityAtomKey>) {
    if let Some(atom) = bitvector_equality_atom_key(term) {
        atoms.insert(atom);
    }
    match term {
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        Bitvector32Term::BitwiseNot(value) => collect_bitvector_atoms(value, atoms),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_atoms(condition, atoms);
            collect_bitvector_atoms(then_term, atoms);
            collect_bitvector_atoms(else_term, atoms);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_atoms(start, atoms);
            collect_bitvector_atoms(end, atoms);
            collect_bitvector_atoms(initial, atoms);
            collect_bitvector_atoms(body, atoms);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_atoms(argument, atoms);
            }
        }
        Bitvector32Term::MemoryLoad(_, pointer) => {
            collect_pointer_offset_bitvector_atoms(&pointer.offset, atoms)
        }
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
    }
}

fn collect_pointer_offset_bitvector_atoms(
    offset: &PointerOffsetTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match offset {
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => collect_bitvector_atoms(value, atoms),
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
    }
}

fn index_quantified_replay_fact(
    mut index: PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>> {
    let Some(key) = quantified_replay_index_key(fact) else {
        return index;
    };
    let mut bucket = index.get(&key).cloned().unwrap_or_default();
    if !bucket.iter().any(|candidate| candidate == fact) {
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

fn index_implication_consequents(
    mut index: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>> {
    let mut antecedents = PersistentSequence::default();
    let mut current = fact;
    while let Proposition::Implies(antecedent, consequent) = current {
        antecedents.push(antecedent.as_ref().clone());
        let candidate = ImplicationCandidate {
            antecedents: antecedents.clone(),
            consequent: consequent.as_ref().clone(),
        };
        let normalized = consequent.clone();
        let mut keys = vec![snapshot_blind_proposition_key(consequent)];
        let normalized_key = snapshot_blind_proposition_key(&normalized);
        if !keys.contains(&normalized_key) {
            keys.push(normalized_key);
        }
        for key in keys {
            let mut bucket = index.get(&key).cloned().unwrap_or_default();
            bucket.push(candidate.clone());
            index = index.with_inserted(key, bucket);
        }
        current = consequent;
    }
    index
}

fn index_proper_conjuncts(
    mut index: PersistentSet<Proposition>,
    fact: &Proposition,
) -> PersistentSet<Proposition> {
    let Proposition::And(left, right) = fact else {
        return index;
    };
    for conjunct in [left.as_ref(), right.as_ref()] {
        index = index.with_value(conjunct.clone());
        index = index_proper_conjuncts(index, conjunct);
    }
    index
}

fn collect_surface_conjunct_leaves(
    proposition: &ClickProposition,
    leaves: &mut Vec<ClickProposition>,
) {
    match proposition {
        ClickProposition::And(left, right) => {
            collect_surface_conjunct_leaves(left, leaves);
            collect_surface_conjunct_leaves(right, leaves);
        }
        leaf => leaves.push(leaf.clone()),
    }
}

fn index_implicit_transport_context(
    mut implicit: PureFactContext,
    fact: &Proposition,
) -> PureFactContext {
    if is_implicit_fact_transport_context(fact) {
        implicit = implicit.assume_proposition(fact.clone());
    }
    implicit
}

fn directly_conflicts_with_normalized_index(
    exact: &PersistentSet<Proposition>,
    fact: &Proposition,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            directly_conflicts_with_normalized_index(exact, left)
                || directly_conflicts_with_normalized_index(exact, right)
        }
        Proposition::ConditionIs(condition, value) => {
            exact.contains(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => exact.contains(body),
        other => exact.contains(&Proposition::Not(Box::new(other.clone()))),
    }
}

fn index_predicate_fact(
    mut index: PersistentMap<String, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<String, PersistentSequence<Proposition>> {
    let mut names = BTreeSet::new();
    collect_fact_predicate_names(fact, &mut names);
    for name in names {
        let mut facts = index.get(&name).cloned().unwrap_or_default();
        facts.push(fact.clone());
        index = index.with_inserted(name, facts);
    }
    index
}

fn collect_fact_predicate_names(fact: &Proposition, names: &mut BTreeSet<String>) {
    match fact {
        Proposition::Predicate { name, .. } => {
            names.insert(name.clone());
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_fact_predicate_names(left, names);
            collect_fact_predicate_names(right, names);
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => collect_fact_predicate_names(body, names),
        _ => {}
    }
}

fn collect_owned_atomic_conjuncts(fact: &Proposition, output: &mut Vec<Proposition>) {
    match fact {
        Proposition::And(left, right) => {
            collect_owned_atomic_conjuncts(left, output);
            collect_owned_atomic_conjuncts(right, output);
        }
        _ => output.push(fact.clone()),
    }
}

#[cfg(test)]
mod tests;
