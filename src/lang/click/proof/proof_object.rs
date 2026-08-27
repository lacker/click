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
        // A branch that ends a bounded region has no derivable continuation:
        // its join rests the parent at its own typed boundary instead.
        let continuation_reachable = derive_execution_join_continuation(
            &self.parent_execution,
            &self.continuation_remaining,
            self.continuation_index,
        )
        .is_some()
            || !matches!(
                self.parent_execution.frontier.region,
                ExecutionRegionKind::Function
            );
        self.sole_feasible_arm().is_some()
            || (continuation_reachable
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
}

/// Derives the exact nonterminal frontier reached after a checked C branch
/// completes, from the branch root's execution and recorded continuation
/// data. See [`ExecutionBranchJoinContinuation`].
fn derive_execution_join_continuation(
    root_execution: &ExecutionProofState,
    continuation_remaining: &Option<Arc<CStatement>>,
    continuation_index: usize,
) -> Option<ExecutionBranchJoinContinuation> {
    let mut continuations = root_execution.frontier.continuations.clone();
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

/// The per-proof constants of an execution proof: which claim is being
/// proved, the source layout it executes, and the entry facts and state
/// that `old(...)` and requirement premises resolve against.
#[derive(Clone, Default)]
pub(in crate::lang::click::proof) struct ExecutionProofConstants {
    pub(in crate::lang::click::proof) proof_site: Option<ProofSite>,
    pub(in crate::lang::click::proof) source_layout: SourceExecutionLayout,
    pub(in crate::lang::click::proof) execution_start_facts: Arc<Vec<Proposition>>,
    pub(in crate::lang::click::proof) function_entry_state: Option<CState>,
    pub(in crate::lang::click::proof) grouped_contract: bool,
}

pub(in crate::lang::click::proof) struct ExecutionProofContext<'a> {
    pub(in crate::lang::click::proof) claim_label: &'a str,
    pub(in crate::lang::click::proof) tactic_index: usize,
    pub(in crate::lang::click::proof) function_block: &'a FunctionBlock,
    pub(in crate::lang::click::proof) function: &'a CFunction,
    pub(in crate::lang::click::proof) parsed_function: &'a syntax::C0Function,
    pub(in crate::lang::click::proof) arguments: &'a [CExpression],
    pub(in crate::lang::click::proof) function_environment: &'a CExecutionEnvironment,
    pub(in crate::lang::click::proof) resource_environment: &'a ResourceEnvironment,
    pub(in crate::lang::click::proof) predicate_environment: &'a PredicateEnvironment,
    pub(in crate::lang::click::proof) click_function_environment: &'a ClickFunctionEnvironment,
    pub(in crate::lang::click::proof) theorem_environment: &'a TheoremEnvironment,
    /// Shared by every context derived from this proof (tactic-index
    /// re-attribution, loop-bound executions), so deriving one is cheap.
    pub(in crate::lang::click::proof) constants: Arc<ExecutionProofConstants>,
}

impl<'a> ExecutionProofContext<'a> {
    /// The state that `old(...)` and `at(function.entry, ...)` resolve to when
    /// a contract clause is lowered at `frontier`.
    pub(in crate::lang::click::proof) fn old_reference_state<'s>(
        &'s self,
        frontier: &'s ExecutionFrontier,
        current_state: &'s CState,
    ) -> &'s CState {
        old_reference_state(
            self.constants.function_entry_state.as_ref(),
            frontier,
            current_state,
        )
    }

    /// The same proof, attributing subsequent diagnostics to `tactic_index`.
    pub(in crate::lang::click::proof) fn with_tactic_index(&self, tactic_index: usize) -> Self {
        Self {
            tactic_index,
            constants: self.constants.clone(),
            ..*self
        }
    }

    /// The same proof executing a function whose frontier loop clauses are
    /// bound: a `loop` tactic runs its one step against the bound block,
    /// the annotated function, and an environment carrying the verified
    /// loop rules, then returns to the enclosing context.
    pub(in crate::lang::click::proof) fn with_loop_binding<'l>(
        &'l self,
        function_block: &'l FunctionBlock,
        function: &'l CFunction,
        function_environment: &'l CExecutionEnvironment,
    ) -> ExecutionProofContext<'l> {
        ExecutionProofContext {
            function_block,
            function,
            function_environment,
            constants: self.constants.clone(),
            ..*self
        }
    }
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
pub(in crate::lang::click::proof) struct ExecutionProofState {
    pub(in crate::lang::click::proof) state: SharedValue<CState>,
    /// Where execution stands: the program point, region, region start
    /// state, and pending continuations.
    pub(in crate::lang::click::proof) frontier: ExecutionFrontier,
    /// The states recorded at program points this path has passed, which
    /// `at(point, ...)` premises resolve against.
    pub(in crate::lang::click::proof) program_point_states: ProgramPointStates,
    /// The surface spellings this path has lowered, paired with their
    /// kernel propositions, so premises can be written as the source wrote
    /// them.
    pub(in crate::lang::click::proof) surface_propositions: SurfacePropositionMap,
    /// Case assumptions introduced on this path by proof-level splits.
    pub(in crate::lang::click::proof) case_assumptions: PersistentSequence<ReplayCaseAssumption>,
    /// Execution facts established by the effects run so far on this path.
    pub(in crate::lang::click::proof) effect_facts: SharedVec<ExecutionPureFact>,
    /// Frontier-local loop clauses and their verified rules, bound on this
    /// path and migrated across joins as arm deltas.
    pub(in crate::lang::click::proof) frontier_loop_clauses: PersistentSequence<StructuralClause>,
    pub(in crate::lang::click::proof) frontier_loop_rules: PersistentSequence<CVerifiedLoopRule>,
    pub(in crate::lang::click::proof) replay: TacticReplayState,
    pub(in crate::lang::click::proof) branch_path: PersistentSequence<String>,
    /// Kernel facts whose checked C-branch Surface spellings must survive a
    /// join for extraction and explicit historical premises.
    pub(in crate::lang::click::proof) branch_surface_facts: PersistentOrderedSet<Proposition>,
    /// Decisions on the currently focused execution lineage. Forks append
    /// one entry in constant time.
    pub(in crate::lang::click::proof) branch_decisions: PersistentSequence<ExecutionBranchDecision>,
    /// Path-local lineages aligned with terminal execution candidates. This
    /// is output-sized Proof provenance, never semantic state in a cursor.
    pub(in crate::lang::click::proof) outcome_branch_decisions:
        Arc<Vec<PersistentSequence<ExecutionBranchDecision>>>,
    pub(in crate::lang::click::proof) last_step_delta: ExecutionProofStepDelta,
    pub(in crate::lang::click::proof) has_empty_execution_branch_leaf: bool,
    /// Whether a structured execution join (a `branch`, a case split, or a
    /// decided path) produced this state: a converging join leaves one path
    /// and no per-path decision, so the fact is recorded here.
    pub(in crate::lang::click::proof) has_structured_branch_history: bool,
    /// The predicates unfolded on this execution path. Distinct from a
    /// goal's `unfolded_predicates`, which are the unfolds visible to one
    /// judgment (a nested scope unfolds locally): this set is path state,
    /// migrated across joins as an arm delta and read by kernel
    /// certification, which exposes these definitions at function entry.
    pub(in crate::lang::click::proof) unfolded_predicates: SharedVec<String>,
}

impl ExecutionProofState {
    /// The read-only execution data lowering and point proofs consult.
    pub(in crate::lang::click::proof) fn view<'s>(
        &'s self,
        context: &'s ExecutionProofContext<'_>,
    ) -> ExecutionView<'s> {
        ExecutionView::new(
            &self.frontier,
            &self.effect_facts,
            &self.program_point_states,
            &self.surface_propositions,
            context.constants.function_entry_state.as_ref(),
        )
    }

    /// The execution state at a proof's entry: the frontier's C state and
    /// replay bag with no branch provenance yet.
    pub(in crate::lang::click::proof) fn at_entry(
        state: CState,
        replay: TacticReplayState,
        frontier: ExecutionFrontier,
        program_point_states: ProgramPointStates,
        surface_propositions: SurfacePropositionMap,
        branch_path: PersistentSequence<String>,
    ) -> Self {
        Self {
            state: state.into(),
            frontier,
            program_point_states,
            surface_propositions,
            case_assumptions: PersistentSequence::default(),
            effect_facts: SharedVec::default(),
            frontier_loop_clauses: PersistentSequence::default(),
            frontier_loop_rules: PersistentSequence::default(),
            replay,
            branch_path,
            branch_surface_facts: PersistentOrderedSet::default(),
            branch_decisions: PersistentSequence::default(),
            outcome_branch_decisions: Arc::new(Vec::new()),
            last_step_delta: ExecutionProofStepDelta::default(),
            has_empty_execution_branch_leaf: false,
            has_structured_branch_history: false,
            unfolded_predicates: SharedVec::default(),
        }
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
pub(super) struct ProofFinalizationView<'p> {
    pub(super) state: &'p CState,
    pub(super) facts: Vec<Proposition>,
    pub(super) replay: &'p TacticReplayState,
    pub(super) frontier: &'p ExecutionFrontier,
    pub(super) execution: &'p ExecutionProofState,
    pub(super) context: &'p ExecutionProofContext<'p>,
    pub(super) unfolded_predicates: &'p SharedVec<String>,
    pub(super) branch_path: &'p PersistentSequence<String>,
    outcome_branch_decisions: &'p [PersistentSequence<ExecutionBranchDecision>],
}

impl ProofFinalizationView<'_> {
    /// The proof-level case decisions recorded on one outcome path, in
    /// decision order: each is a surface condition and the arm taken.
    pub(super) fn path_case_decisions(&self, path_index: usize) -> Vec<(ClickProposition, bool)> {
        self.outcome_branch_decisions
            .get(path_index)
            .map(|decisions| {
                decisions
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
    /// The facts the partitioning statement introduced on each lane (a
    /// callee's instantiated `ensures`): the bounded evidence a later
    /// proof-level case split uses to exclude a lane.
    introduced_facts: [Vec<Proposition>; 2],
    common_facts: ProofFacts,
    parent_unfolds: PersistentOrderedSet<String>,
    parent_execution: Arc<ExecutionProofState>,
    execution_start_state: CState,
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

    /// The execution proof's per-proof context, when this is one.
    pub(in crate::lang::click::proof) fn execution_context(
        &self,
    ) -> Option<&ExecutionProofContext<'a>> {
        match self.context.as_ref() {
            ProofContext::Execution(context) => Some(context),
            _ => None,
        }
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
                .map(|execution| execution.unfolded_predicates.as_slice())
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
        SimpleProofStep::Step => "step",
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

impl ProofContext<'_> {
    fn claim_label(&self) -> &str {
        match self {
            Self::Pure(context) => context.claim_label,
            Self::Point(context) => context.claim_label,
            Self::Execution(context) => context.claim_label,
        }
    }
}

mod construction;
mod execution_joins;
mod execution_statements;
mod fact_index;
mod outcomes_and_focus;
mod point_steps;
mod replay_boundary;
mod resource_steps;
mod scope;
mod smart_closures;
mod smart_execution;
mod splits_and_scopes;
mod step_application;
mod surface_lowering;

#[cfg(test)]
mod tests;
