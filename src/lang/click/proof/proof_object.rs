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

/// Two open proposition branches owned by one audited structural operation.
///
/// Branch-local assumptions exist only inside this container. The enclosing
/// `Proof` advances when both arms are complete and `join` records their exact
/// retained certificates in one structured simple step.
#[derive(Clone)]
pub(super) struct ProofBranches<'a> {
    root: Proof<'a>,
    structure: ProofBranchStructure,
    /// The recorded split: allocated with the labeled child goal ids below
    /// when the branches were created, in rule order.
    split: SplitId,
    /// Each arm's recorded child goal id, then-arm before else-arm.
    child_goals: [GoalId; 2],
    /// Each arm's unique entry provenance marker. The join accepts only
    /// descendants that pass through their own arm's exact marker, so an arm
    /// checked under another split of the same root cannot be spliced in.
    entries: [ProofCheckpoint<'a>; 2],
    arms: [Proof<'a>; 2],
}

/// Two exhaustive terminal-execution outcome partitions selected by one
/// proof-level condition.
///
/// Unlike [`ProofBranches`], these arms retain execution-frontier goals and
/// own disjoint subsets of an already-checked function execution. Branch-local
/// facts can therefore justify terminal simple steps without being exposed to
/// incompatible outcomes. The audited join restores the complete execution,
/// records one structured `If`, and combines matching checked-frame authority
/// into one ordered resource transition.
struct ExecutionOutcomeProofBranches<'a> {
    root: Proof<'a>,
    /// The recorded split with each arm's child goal id and entry marker,
    /// then-arm before else-arm.
    split: SplitId,
    child_goals: [GoalId; 2],
    entries: [ProofCheckpoint<'a>; 2],
    condition: ClickProposition,
    arms: [Proof<'a>; 2],
    root_post_execution_count: usize,
}

/// Feasible arms of one checked C `if` frontier.
///
/// Entering the container performs the audited condition transition and C
/// frontier movement once. Arm bodies then extend the retained `Proof`
/// descendants; a join owns the corresponding structured certificate node.
#[derive(Clone)]
pub(super) struct ExecutionProofBranches<'a> {
    root: Proof<'a>,
    /// The recorded split with each arm's child goal id and entry provenance
    /// marker, then-arm before else-arm. This identity lives on the
    /// container, never on an arm value: a spliced foreign arm must not be
    /// able to carry its own credentials into this split's join.
    split: SplitId,
    child_goals: [GoalId; 2],
    entries: [Option<ProofCheckpoint<'a>>; 2],
    statement_index: usize,
    continuation_index: usize,
    continuation_remaining: Option<Arc<CStatement>>,
    execution_start_state: CState,
    initial_continuation_depth: usize,
    arms: [Option<ExecutionProofArm<'a>>; 2],
}

#[derive(Clone)]
struct ExecutionProofArm<'a> {
    proof: Proof<'a>,
    introduced_facts: PersistentOrderedSet<Proposition>,
    introduced_effect_facts: Vec<ExecutionPureFact>,
    introduced_function_entry_prerequisites: PersistentOrderedSet<Proposition>,
    introduced_function_entry_derivations: PersistentOrderedSet<Theorem>,
    introduced_unfolded_predicates: PersistentOrderedSet<String>,
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

#[derive(Clone)]
enum ProofBranchStructure {
    Cases { disjunction: ClickProposition },
    If { condition: ClickProposition },
}

fn explicit_linear_step(tactic: &ProofTactic) -> Option<SimpleProofStep> {
    let certificate = ProofCertificate::from_proof_tactics(std::slice::from_ref(tactic)).ok()?;
    let [step] = certificate.steps() else {
        return None;
    };
    matches!(
        step,
        SimpleProofStep::ApplyTheoremUsing { .. }
            | SimpleProofStep::UnfoldPredicate(_)
            | SimpleProofStep::Witness(_)
            | SimpleProofStep::Choose(_)
            | SimpleProofStep::Assumption
            | SimpleProofStep::Extract(_)
            | SimpleProofStep::Normalize
            | SimpleProofStep::Intro
            | SimpleProofStep::Split
            | SimpleProofStep::Left
            | SimpleProofStep::Right
            | SimpleProofStep::Enumerate
            | SimpleProofStep::Contradiction(_)
            | SimpleProofStep::Rewrite(_)
            | SimpleProofStep::TransportUsing { .. }
            | SimpleProofStep::InstantiateUsing { .. }
    )
    .then(|| step.clone())
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

fn script_contains_linear_search(tactics: &[ProofTactic]) -> bool {
    tactics.iter().any(|tactic| match tactic {
        ProofTactic::ApplyTheorem(_) | ProofTactic::Simp => true,
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
    if script_contains_linear_search(tactics) {
        linear_script_is_supported(tactics)
    } else {
        ProofCertificate::from_proof_tactics(tactics).is_ok()
    }
}

fn source_proof_is_supported(proof: &SourceProof) -> bool {
    match proof {
        SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => true,
        SourceProof::Script(tactics) => {
            if script_contains_linear_search(tactics) {
                linear_script_is_supported(tactics)
            } else {
                ProofCertificate::from_proof_tactics(tactics).is_ok()
            }
        }
        SourceProof::Tactic(SmartTactic::Frame) => false,
    }
}

fn certificate_leaves_end_in_frame(certificate: &ProofCertificate) -> bool {
    match certificate.steps().last() {
        Some(SimpleProofStep::FrameUsing { region: None, .. }) => true,
        Some(SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        }) => {
            certificate_leaves_end_in_frame(then_proof)
                && certificate_leaves_end_in_frame(else_proof)
        }
        _ => false,
    }
}

fn certificate_branch_conditions(
    certificate: &ProofCertificate,
    conditions: &mut Vec<ClickProposition>,
) {
    for step in certificate.steps() {
        if let SimpleProofStep::If {
            condition,
            then_proof,
            else_proof,
        } = step
        {
            if !conditions.contains(condition) {
                conditions.push(condition.clone());
            }
            certificate_branch_conditions(then_proof, conditions);
            certificate_branch_conditions(else_proof, conditions);
        }
    }
}

fn contextual_frame_leaf_certificates(
    certificate: &ProofCertificate,
    leaves: &mut Vec<ProofCertificate>,
) {
    if let [
        SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        },
    ] = certificate.steps()
    {
        contextual_frame_leaf_certificates(then_proof, leaves);
        contextual_frame_leaf_certificates(else_proof, leaves);
    } else {
        leaves.push(certificate.clone());
    }
}

fn flatten_path_independent_frame_candidate(candidate: ProofCertificate) -> ProofCertificate {
    let mut leaves = Vec::new();
    contextual_frame_leaf_certificates(&candidate, &mut leaves);
    match leaves.first() {
        Some(first) if leaves.iter().all(|leaf| leaf.steps() == first.steps()) => first.clone(),
        _ => candidate,
    }
}

fn frame_candidate_needs_snapshot_legacy(certificate: &ProofCertificate) -> bool {
    certificate.steps().iter().any(|step| match step {
        SimpleProofStep::Have { proof, .. } => {
            let ambiguous_snapshot_theorem_suffix = matches!(
                proof.steps(),
                [
                    ..,
                    SimpleProofStep::ApplyTheoremUsing { application, .. },
                    SimpleProofStep::Assumption
                ] if application.arguments.iter().any(contains_at_expression)
                    && !matches!(
                        application.name.as_str(),
                        "int32_ge_implies_reversed_le" | "int32_le_implies_reversed_ge"
                    )
            );
            ambiguous_snapshot_theorem_suffix || frame_candidate_needs_snapshot_legacy(proof)
        }
        SimpleProofStep::Open { proof, .. } => frame_candidate_needs_snapshot_legacy(proof),
        SimpleProofStep::If {
            then_proof,
            else_proof,
            ..
        } => {
            frame_candidate_needs_snapshot_legacy(then_proof)
                || frame_candidate_needs_snapshot_legacy(else_proof)
        }
        SimpleProofStep::Cases {
            left_proof,
            right_proof,
            ..
        } => {
            frame_candidate_needs_snapshot_legacy(left_proof)
                || frame_candidate_needs_snapshot_legacy(right_proof)
        }
        SimpleProofStep::Branch {
            then_proof,
            else_proof,
            ..
        } => {
            frame_candidate_needs_snapshot_legacy(then_proof)
                || frame_candidate_needs_snapshot_legacy(else_proof)
        }
        _ => false,
    })
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ProofArm {
    Left,
    Right,
}

impl ProofArm {
    fn index(self) -> usize {
        match self {
            Self::Left => 0,
            Self::Right => 1,
        }
    }
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
    /// Predicate definitions activated by accepted proof-local unfold steps.
    /// Inherited point/execution names remain in their shared context; this is
    /// only the local delta, so creating a root never rebuilds proof history.
    /// Forks share both the insertion order and exact-membership index.
    unfolded_predicates: PersistentOrderedSet<String>,
    goals: ProofGoals,
    added_facts: Arc<Vec<Proposition>>,
    checked_facts: Arc<Vec<Proposition>>,
}

/// Identity of one open obligation within a proof lineage.
///
/// Allocation is monotonic per lineage. Ids allocated after divergent forks
/// may collide numerically; identity comparison is meaningful only along one
/// ancestry chain or against the recorded structure that allocated the id.
/// See the goal and split identity rules in `issues/proof-object-api.md`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct GoalId(u64);

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
    /// Creates the root goal set of a fresh proof: one open goal.
    fn root(goal: Goal) -> Self {
        Self {
            open: PersistentMap::default().with_inserted(GoalId(1), goal),
            next_id: 2,
        }
    }

    /// The unique open goal, while every proof owns at most one.
    ///
    /// Multi-goal states arrive with audited splits; readers that can only
    /// interpret one focused goal must go through here so the single-goal
    /// assumption stays in one place.
    fn sole(&self) -> Option<(GoalId, &Goal)> {
        debug_assert!(
            self.open.len() <= 1,
            "sole-goal reader on a multi-goal proof state"
        );
        self.open.iter().next().map(|(id, goal)| (*id, goal))
    }

    /// Replaces the focused goal's content while preserving its identity.
    /// This is the successor shape of a goal-preserving refinement rule.
    fn replace_sole(&self, goal: Goal) -> Self {
        let Some((id, _)) = self.sole() else {
            unreachable!("goal refinement requires an open goal");
        };
        Self {
            open: self.open.with_inserted(id, goal),
            next_id: self.next_id,
        }
    }

    /// Retires the focused goal: the discharge shape of a goal-closing rule.
    /// The id is never reallocated within this lineage.
    fn discharge_sole(&self) -> Self {
        let Some((id, _)) = self.sole() else {
            unreachable!("goal discharge requires an open goal");
        };
        Self {
            open: self.open.without_key(&id),
            next_id: self.next_id,
        }
    }

    /// Allocates the labeled child goal collections of an audited split in
    /// rule order (for a branch: then before else).
    ///
    /// Each child owns the parent obligation's content under a fresh recorded
    /// id. The parent proof's own goal collection is untouched: its id is
    /// retired only when the join commits, so dropping the split leaves the
    /// root the unchanged authority. Divergent splits of one root allocate
    /// numerically colliding ids — identity across splits is carried by each
    /// arm's entry provenance marker, never by id magnitude (identity rule 3).
    fn branch_children<const ARMS: usize>(&self) -> (SplitId, [GoalId; ARMS], [Self; ARMS]) {
        let Some((_, goal)) = self.sole() else {
            unreachable!("an audited split requires an open goal");
        };
        let split = SplitId(self.next_id);
        let ids: [GoalId; ARMS] = std::array::from_fn(|arm| GoalId(self.next_id + 1 + arm as u64));
        let children: [Self; ARMS] = std::array::from_fn(|arm| Self {
            open: PersistentMap::default().with_inserted(ids[arm], goal.clone()),
            next_id: self.next_id + 1 + ARMS as u64,
        });
        (split, ids, children)
    }

    /// Retains the focused goal under an updated path-local context,
    /// preserving identity, kind, and selection/content. This is the
    /// successor shape of a fact-adding or snapshot-updating rule.
    fn with_sole_context(&self, context: GoalContext) -> Self {
        let Some((id, goal)) = self.sole() else {
            unreachable!("a context successor requires an open goal");
        };
        Self {
            open: self.open.with_inserted(id, goal.with_context(context)),
            next_id: self.next_id,
        }
    }

    /// Retains the focused goal under updated facts, preserving any
    /// execution snapshot it already borrowed.
    fn with_sole_facts(&self, facts: ProofFacts) -> Self {
        let Some((_, goal)) = self.sole() else {
            unreachable!("a fact successor requires an open goal");
        };
        self.with_sole_context(GoalContext {
            facts,
            execution: goal.context().execution.clone(),
        })
    }

    /// Retains the focused goal under an updated execution snapshot and
    /// facts. The successor preserves the goal's kind: a nested proposition
    /// judgment stated at a frontier may also refine facts.
    fn replace_sole_execution(&self, facts: ProofFacts, execution: ExecutionProofState) -> Self {
        self.with_sole_context(GoalContext {
            facts,
            execution: Some(Arc::new(execution)),
        })
    }

    /// The strict frontier successor: the focused goal must be an execution
    /// frontier. C-advancing rules use this shape; rules legal on nested
    /// proposition judgments use [`Self::replace_sole_execution`].
    fn replace_sole_frontier(&self, facts: ProofFacts, execution: ExecutionProofState) -> Self {
        let Some((_, Goal::Frontier(_))) = self.sole() else {
            unreachable!("a frontier transition requires an open frontier goal");
        };
        self.replace_sole_execution(facts, execution)
    }

    /// Discharges the focused goal when `complete` holds; otherwise the goal
    /// is retained under the updated facts. This is the successor shape of a
    /// fact-adding rule whose new fact may exactly close a proposition goal.
    fn discharged_if(&self, complete: bool, facts: ProofFacts) -> Self {
        if complete {
            self.discharge_sole()
        } else {
            self.with_sole_facts(facts)
        }
    }

    /// Discharges the goal when its proposition was established; otherwise
    /// retains it under the updated facts and execution snapshot.
    fn discharged_if_or_execution(
        &self,
        complete: bool,
        facts: ProofFacts,
        execution: ExecutionProofState,
    ) -> Self {
        if complete {
            self.discharge_sole()
        } else {
            self.replace_sole_execution(facts, execution)
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
    last_step_delta: ExecutionProofStepDelta,
}

#[derive(Clone, Default)]
struct ExecutionProofStepDelta {
    function_entry_prerequisites: Vec<Proposition>,
    function_entry_derivations: Vec<Theorem>,
    unfolded_predicates: Vec<String>,
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
}

/// The path-local semantic context owned by one goal.
///
/// Facts and any execution snapshot travel together: sibling goals produced
/// by a split each own their path's context, sharing unchanged persistent
/// structure with the ancestor. `ProofState` retains only lineage-wide data.
#[derive(Clone)]
struct GoalContext {
    facts: ProofFacts,
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
    /// The judgment's path-local facts plus, when stated at an execution
    /// point, the immutable snapshot borrowed by identity from the frontier
    /// that stated it. A proposition goal can never publish a changed
    /// frontier through this context.
    context: GoalContext,
}

impl Goal {
    fn proposition_in(context: GoalContext, kernel: Proposition) -> Self {
        Self::Proposition(PropositionGoal {
            kernel: Arc::new(kernel),
            surface: None,
            context,
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
            context,
        })
    }

    fn context(&self) -> &GoalContext {
        match self {
            Self::Proposition(goal) => &goal.context,
            Self::Frontier(goal) => &goal.context,
        }
    }

    fn with_context(&self, context: GoalContext) -> Self {
        match self {
            Self::Proposition(goal) => Self::Proposition(PropositionGoal {
                kernel: goal.kernel.clone(),
                surface: goal.surface.clone(),
                context,
            }),
            Self::Frontier(goal) => Self::Frontier(FrontierGoal {
                selection: goal.selection,
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
enum EffectGoalSelection {
    None,
    One(usize),
    All,
}

/// Private authority that the ordered outcome finalizer may consume without
/// proving the same function effect a second time.
///
/// Only `Proof::apply_execution_frame_using` constructs this value, after it
/// checks every selected effect against every owned execution outcome.
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
    normalized_exact: PersistentSet<Proposition>,
    by_snapshot_blind: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>>,
    by_quantified_replay: PersistentMap<QuantifiedReplayKey, PersistentSequence<Proposition>>,
    implications_by_consequent:
        PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    assumptions: PureFactContext,
    implicit_transport_assumptions: PureFactContext,
    direct_lowering_assumptions: PureFactContext,
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

impl<'a> Proof<'a> {
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
                unfolded_predicates: PersistentOrderedSet::default(),
                goals: ProofGoals::root({
                    let context = GoalContext {
                        facts,
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
                depth: 0,
            }),
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
                unfolded_predicates: PersistentOrderedSet::default(),
                goals: ProofGoals::root(goal(GoalContext {
                    facts,
                    execution: None,
                })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
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
            }) => EffectGoalSelection::All,
            Some(ProofSite::FunctionClaim {
                claim: CProofClaim::Effect(index),
                ..
            }) => EffectGoalSelection::One(*index),
            _ => EffectGoalSelection::None,
        };
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
                unfolded_predicates: PersistentOrderedSet::default(),
                goals: ProofGoals::root(Goal::Frontier(FrontierGoal {
                    selection: effect_goals,
                    context: GoalContext {
                        facts: ProofFacts::from_ordered(&pure_facts),
                        execution: Some(Arc::new(ExecutionProofState {
                            state: state.into(),
                            replay,
                            branch_path,
                            last_step_delta: ExecutionProofStepDelta::default(),
                        })),
                    },
                })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
        }
    }

    /// The unique open goal, while every proof owns at most one. Readers
    /// that can only interpret a single focused goal go through here so the
    /// single-goal assumption stays in one place until splits arrive.
    fn sole_goal(&self) -> Option<&Goal> {
        self.state.goals.sole().map(|(_, goal)| goal)
    }

    /// The focused goal's path-local execution context, shared by identity
    /// with the frontier that created it.
    fn goal_execution(&self) -> Option<&Arc<ExecutionProofState>> {
        self.sole_goal()?.context().execution.as_ref()
    }

    /// The focused goal's path-local fact context. Every caller is a
    /// checked operation or search query on an open goal: `apply_step` and
    /// the structural operations reject discharged proofs first.
    fn facts(&self) -> &ProofFacts {
        match self.sole_goal() {
            Some(goal) => &goal.context().facts,
            None => unreachable!("fact queries require an open goal"),
        }
    }

    /// The focused goal's context with updated facts, for refinement rules
    /// that change goal content and facts together.
    fn refined_context(&self, facts: ProofFacts) -> GoalContext {
        GoalContext {
            facts,
            execution: self.goal_execution().cloned(),
        }
    }

    fn execution(&self) -> Option<&ExecutionProofState> {
        self.goal_execution().map(Arc::as_ref)
    }

    /// The identity of the unique open goal, if one remains. Joins compare
    /// this against their recorded child goal ids; comparisons are only
    /// meaningful within one lineage or recorded split (identity rule 3).
    fn sole_goal_id(&self) -> Option<GoalId> {
        self.state.goals.sole().map(|(id, _)| id)
    }

    #[cfg(test)]
    fn goals_next_id(&self) -> u64 {
        self.state.goals.next_id
    }

    pub(super) fn goal(&self) -> Option<&Proposition> {
        match self.sole_goal() {
            Some(Goal::Proposition(goal)) => Some(&goal.kernel),
            _ => None,
        }
    }

    fn surface_goal(&self) -> Option<&ClickProposition> {
        match self.sole_goal() {
            Some(Goal::Proposition(goal)) => goal.surface.as_deref(),
            _ => None,
        }
    }

    /// Number of selected function-effect obligations represented by this
    /// frontier without materializing their clauses.
    #[cfg(test)]
    fn effect_goal_count(&self) -> usize {
        let Some(Goal::Frontier(FrontierGoal { selection, .. })) = self.sole_goal() else {
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
        if !matches!(self.context.as_ref(), ProofContext::Point(_))
            || !matches!(self.sole_goal(), Some(Goal::Frontier(_)))
        {
            return Err(
                self.step_error("a proposition goal can be focused only from a point frontier")
            );
        }
        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                unfolded_predicates: self.state.unfolded_predicates.clone(),
                goals: ProofGoals::root({
                    let context = GoalContext {
                        facts: self.facts().clone(),
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
                depth: 0,
            }),
        })
    }

    /// Lowers and selects one externally owned Surface Click obligation from
    /// a point frontier. The returned proof shares every accumulated checked
    /// fact but owns fresh provenance for that obligation's closing steps.
    fn focus_point_surface_goal(&self, goal: &ClickProposition) -> Result<Self, ClickError> {
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
        if goals.is_empty() {
            return Err(self.step_error("point obligation completion requires at least one goal"));
        }
        if !matches!(self.context.as_ref(), ProofContext::Point(_))
            || !matches!(self.sole_goal(), Some(Goal::Frontier(_)))
        {
            return Err(self.step_error("point obligations require an open point frontier"));
        }
        let mut steps = self.certificate().steps().to_vec();
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
        for name in &self.state.unfolded_predicates {
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
        if self.state.goals.is_discharged() {
            return Err(self.step_error("a tactic follows a goal-closing step"));
        }

        let next_state = match &step {
            SimpleProofStep::Mark(name) => self.apply_execution_mark(name),
            SimpleProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            SimpleProofStep::Step => self.apply_execution_statement_using(&[]),
            SimpleProofStep::StepUsing(premises) => self.apply_execution_statement_using(premises),
            SimpleProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            SimpleProofStep::UnfoldPredicate(name) => self.apply_predicate_unfold(name),
            SimpleProofStep::UnfoldResource(resource) => {
                self.apply_execution_resource_unfold(resource)
            }
            SimpleProofStep::FoldResource(resource) => self.apply_execution_resource_fold(resource),
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
                self.apply_execution_frame_using(region.as_ref(), premises, origin)
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
                depth: self.node.depth + 1,
            }),
        })
    }

    fn selected_effect_indices(
        &self,
        context: &ExecutionProofContext<'_>,
    ) -> Result<Vec<usize>, ClickError> {
        let Some(Goal::Frontier(FrontierGoal { selection, .. })) = self.sole_goal() else {
            return Err(self.step_error("`frame using` requires an execution effect goal"));
        };
        let effect_count = context.function_block.effects().len();
        let indices = match *selection {
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

    /// Whether this frame step is inside the deliberately narrow checked
    /// terminal-operation slice. Returning `false` preserves the legacy path
    /// for empty mutable function frames whose current surface meaning still
    /// includes ambient-fact selection.
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
    /// private authority for the ordered outcome finalizer.
    #[inline(never)]
    fn apply_execution_frame_using(
        &self,
        region: Option<&CodeRegionRef>,
        premises: &[ClickProposition],
        origin: Option<ProofStepOrigin>,
    ) -> Result<ProofState, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`frame using` requires an execution proof"));
        };
        self.require_execution_frontier("`frame using`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if !execution.replay.is_at_function_exit() {
            return Err(self.step_error("`frame using` requires function exit"));
        }

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
                    unfolded_predicates: self.state.unfolded_predicates.clone(),
                    goals: self
                        .state
                        .goals
                        .replace_sole_frontier(self.facts().clone(), execution),
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
                surface_certificate: Some(ProofCertificate::from_steps(vec![
                    SimpleProofStep::FrameUsing {
                        region: region.cloned(),
                        premises: premises.to_vec(),
                    },
                ])),
            },
        );
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.replace_sole(Goal::Frontier(FrontierGoal {
                selection: EffectGoalSelection::None,
                context: GoalContext {
                    facts: self.facts().clone(),
                    execution: Some(Arc::new(execution)),
                },
            })),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    /// Applies a contextual frame candidate through checked simple steps.
    /// A branch-shaped candidate partitions the owned terminal outcomes and
    /// recursively checks each leaf; it never treats a proof condition as a
    /// globally available fact across incompatible paths.
    fn apply_contextual_frame_candidate_certificate(
        &self,
        certificate: &ProofCertificate,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        let [
            SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            },
        ] = certificate.steps()
        else {
            let checkpoint = self.checkpoint();
            let checked = self.check_flat_contextual_frame_candidate(certificate, origin)?;
            let retained = checked.certificate_since(&checkpoint)?;
            return checked.with_deferred_frame_surface_certificate(retained);
        };
        let branches = self.begin_execution_outcome_if(condition.clone())?;
        let branches = branches.check_arm_certificate(0, then_proof, origin)?;
        let branches = branches.check_arm_certificate(1, else_proof, origin)?;
        branches.join()
    }

    /// Checks one flat planner candidate while letting the owned nested Proof
    /// decide whether a theorem application already closed a generated
    /// `have`. Surface lowering historically appends `assumption` because a
    /// point theorem may merely add an equivalent snapshot fact; when it adds
    /// the exact goal, that suffix would instead follow a completed proof.
    fn check_flat_contextual_frame_candidate(
        &self,
        certificate: &ProofCertificate,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        let mut checked = self.clone();
        for step in certificate.steps() {
            let SimpleProofStep::Have { proposition, proof } = step else {
                checked = checked.apply_step_with_origin(step.clone(), origin)?;
                continue;
            };
            let body_steps = proof.steps();
            let theorem_assumption_suffix = matches!(
                body_steps,
                [
                    ..,
                    SimpleProofStep::ApplyTheoremUsing { .. },
                    SimpleProofStep::Assumption
                ]
            );
            let mut scope = checked.begin_have(proposition.clone())?;
            if theorem_assumption_suffix {
                for body_step in &body_steps[..body_steps.len() - 1] {
                    scope = scope.apply_step(body_step.clone())?;
                }
                if !scope.body.is_complete() {
                    scope = scope.apply_step(SimpleProofStep::Assumption)?;
                }
            } else {
                scope.body = scope.body.check_certificate_with_origin(proof, origin)?;
            }
            checked = scope.join()?;
        }
        Ok(checked)
    }

    /// Associates a flat candidate's complete checked certificate with its
    /// terminal frame deferral. This preserves the source ordering of earlier
    /// deferred steps while allowing the drain to retain the certificate
    /// without semantically replaying it.
    fn with_deferred_frame_surface_certificate(
        mut self,
        certificate: ProofCertificate,
    ) -> Result<Self, ClickError> {
        let mut execution = self.execution().cloned().ok_or_else(|| {
            self.step_error("checked frame certificate lost its execution frontier")
        })?;
        let mut deferred = execution
            .replay
            .post_execution_tactics
            .pop()
            .ok_or_else(|| self.step_error("checked frame retained no terminal deferral"))?;
        let PostExecutionTactic::CheckedFrameUsing {
            surface_certificate,
            ..
        } = &mut deferred.tactic
        else {
            return Err(
                self.step_error("checked frame certificate did not end in checked frame authority")
            );
        };
        *surface_certificate = Some(certificate);
        execution.replay.post_execution_tactics.push(deferred);
        let facts = self.facts().clone();
        let mut state = (*self.state).clone();
        state.goals = state.goals.replace_sole_frontier(facts, execution);
        self.state = Arc::new(state);
        Ok(self)
    }

    /// Uses the existing contextual footprint planner only to select Surface
    /// simple steps. The returned certificate has performed no semantic
    /// transition; its flat or branch-shaped candidate still has to advance
    /// through the checked `Proof` operations above.
    fn select_contextual_frame_candidate(&self) -> Result<Option<ProofCertificate>, ClickError> {
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
        if self.node.depth == 0
            && (execution.paths().len() > 1 || execution_state.replay.has_structured_branch_history)
        {
            // A compatibility adapter created after a legacy branch owns the
            // outcomes but not the branch Proof that partitions them. Leave
            // that context to the legacy frame path; a joined Proof retains
            // its `If` certificate and can check each candidate arm itself.
            return Ok(None);
        }
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
            let mut combined = Vec::new();
            for effect_index in &effect_indices {
                for derivation in plan_effect_clause_derivations(
                    context.claim_label,
                    path_index,
                    path.effect_facts(),
                    &path_facts,
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
        let skeleton = surface_branch_skeleton(self.certificate().steps());
        let mut construction_replay = execution_state.replay.clone();
        let mut branch_conditions = Vec::new();
        certificate_branch_conditions(
            &ProofCertificate::from_steps(skeleton.clone()),
            &mut branch_conditions,
        );
        for condition in &branch_conditions {
            let negated = ClickProposition::Not(Box::new(condition.clone()));
            let mut surface_spellings = vec![condition.clone(), negated.clone()];
            for candidate in [
                reverse_surface_comparison(condition),
                reverse_surface_comparison(&negated),
            ]
            .into_iter()
            .flatten()
            {
                if !surface_spellings.contains(&candidate) {
                    surface_spellings.push(candidate);
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
                for surface in &surface_spellings {
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
        construction_replay.proof_certificate_builder = ProofCertificateBuilder {
            steps: skeleton,
            certificate_facts: ProofFactStore::from_ordered(available),
            last_step_entry: execution_state
                .replay
                .proof_certificate_builder
                .last_step_entry
                .clone(),
            ..ProofCertificateBuilder::default()
        }
        .into();
        construct_simple_step_for_planned_operation(
            &mut construction_replay,
            &execution_state.state,
            context.function_block,
            context.parsed_function.parameters(),
            context.arguments,
            ConstructionEnvironments {
                predicate_environment: context.predicate_environment,
                click_function_environment: context.click_function_environment,
            },
            &ConstructionEvidence::CertifiedFrame(path_derivations),
        );
        let construction =
            std::mem::take(&mut construction_replay.proof_certificate_builder).into_value();
        if let Some(blocker) = construction.blocker {
            return Err(self.step_error(format!(
                "smart frame candidate construction failed: {blocker}"
            )));
        }
        let candidate = flatten_path_independent_frame_candidate(ProofCertificate::from_steps(
            construction.steps,
        ));
        if candidate.steps().is_empty() || !certificate_leaves_end_in_frame(&candidate) {
            return Ok(None);
        }
        Ok(Some(candidate))
    }

    /// Reports whether a source-owned terminal frame can advance this exact
    /// checked Proof. This is a capability query only; a false result leaves
    /// the proof available for a legacy compatibility fallback.
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
    /// simple certificate directly to this Proof. Successful search returns
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
            self.sole_goal(),
            Some(Goal::Frontier(FrontierGoal {
                selection: EffectGoalSelection::None,
                ..
            }))
        ) {
            return Ok(None);
        }
        if self.node.depth > 0 {
            let step = SimpleProofStep::FrameUsing {
                region: None,
                premises: Vec::new(),
            };
            match self.apply_step_at(step, tactic_index, source_index) {
                Ok(framed) => return Ok(Some(framed)),
                Err(error) if crate::instrumentation::deadline_exceeded() => return Err(error),
                Err(_) => {}
            }
        }
        // An unqualified `frame()` is a smart operation, even when an empty
        // `FrameUsing` happens to prove the selected effect. A compatibility
        // root has no retained Proof history for earlier deferred source
        // steps, so its contextual candidate must preserve the explicit
        // resource facts those steps need. Native Proof descendants already
        // own their history and keep the cheap exact candidate as the first
        // choice.
        let Some(candidate) = self.select_contextual_frame_candidate()? else {
            return Ok(None);
        };
        if frame_candidate_needs_snapshot_legacy(&candidate) {
            // Snapshot-qualified theorem spellings can add a kernel fact that
            // is exact in this recorded lowering context but still require a
            // trailing `assumption` when replayed from fresh source. Until
            // Proof owns that stable surface identity, leave this candidate
            // to the compatibility path rather than retain an ambiguous node.
            return Ok(None);
        }
        let origin = Some(ProofStepOrigin {
            tactic_index,
            source_index,
        });
        match self.apply_contextual_frame_candidate_certificate(&candidate, origin) {
            Ok(checked) => Ok(Some(checked)),
            Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
            Err(_) => Ok(None),
        }
    }

    #[inline(never)]
    fn apply_assumption(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`assumption` requires a proposition goal")?;
        let available = match self.context.as_ref() {
            ProofContext::Point(_) => self.facts().pure_replay_available(goal),
            ProofContext::Pure(_) | ProofContext::Execution(_) => self.facts().contains(goal),
        };
        if !available {
            return Err(self.step_error(format!(
                "`assumption` requires the exact current goal as an available fact: {:?}",
                goal
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_normalize(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`normalize` requires a proposition goal")?;
        if !normalizes_context_free(goal) {
            return Err(self.step_error(format!(
                "`normalize` requires a context-free true goal: {:?}",
                goal
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_intro(&self) -> Result<ProofState, ClickError> {
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Implies(_, consequent)) => Some(consequent.as_ref().clone()),
            _ => None,
        };
        let goal = self
            .proposition_goal("`intro` requires a proposition goal")?
            .clone();
        let (goal, introduced) = match goal {
            Proposition::Implies(antecedent, consequent) => (*consequent, Some(*antecedent)),
            Proposition::ForAll { body, .. } => (*body, None),
            Proposition::Not(body) => (
                Proposition::ConditionIs(ConditionTerm::Constant(false), true),
                Some(*body),
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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.replace_sole({
                let context = self.refined_context(facts);
                surface_goal
                    .map(|surface| {
                        Goal::surface_proposition_in(context.clone(), goal.clone(), surface)
                    })
                    .unwrap_or_else(|| Goal::proposition_in(context, goal))
            }),
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
        })
    }

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

    #[inline(never)]
    fn apply_left(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`left` requires a proposition goal")?;
        let Proposition::Or(left, _) = goal else {
            return Err(
                self.step_error(format!("`left` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(left)
            && !condition_polarity_spellings(left)
                .iter()
                .any(|spelling| self.facts().contains(spelling))
        {
            return Err(self.step_error(format!(
                "`left` requires its selected disjunct as an exact fact: {left:?}"
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_right(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`right` requires a proposition goal")?;
        let Proposition::Or(_, right) = goal else {
            return Err(
                self.step_error(format!("`right` requires a disjunction goal, got {goal:?}"))
            );
        };
        if !self.facts().contains(right)
            && !condition_polarity_spellings(right)
                .iter()
                .any(|spelling| self.facts().contains(spelling))
        {
            return Err(self.step_error(format!(
                "`right` requires its selected disjunct as an exact fact: {right:?}"
            )));
        }
        Ok(self.closed_state())
    }

    #[inline(never)]
    fn apply_enumerate(&self) -> Result<ProofState, ClickError> {
        let goal = self.proposition_goal("`enumerate` requires a proposition goal")?;
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal) else {
            return Err(self.step_error(format!(
                "`enumerate` requires a constant-bounded universal goal, got {goal:?}"
            )));
        };
        for (_, instance) in instances {
            if !normalizes_context_free(&instance) && !self.facts().contains(&instance) {
                return Err(self.step_error(format!(
                    "`enumerate` requires an unavailable exact instance: {instance:?}"
                )));
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

    /// Opens an exact disjunction into two immutable proof branches.
    ///
    /// This is a structural kernel operation, not a smart tactic: it accepts
    /// no derived or ambiently provable disjunction. Each arm receives only
    /// its corresponding exact disjunct in addition to the shared facts.
    pub(super) fn begin_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<ProofBranches<'a>, ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`cases` follows a completed proof"));
        }
        self.proposition_goal("`cases` requires a proposition goal")?;
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        if !self.facts().contains(&kernel) {
            return Err(self.step_error(format!(
                "`cases` requires its exact disjunction as an available fact: {kernel:?}"
            )));
        }
        let Proposition::Or(left, right) = kernel else {
            return Err(self.step_error(format!("`cases` requires a disjunction, got {kernel:?}")));
        };
        let (split, child_goals, [left_goals, right_goals]) =
            self.state.goals.branch_children::<2>();
        let arms = [
            self.branch_arm(*left, left_goals),
            self.branch_arm(*right, right_goals),
        ];
        Ok(ProofBranches {
            root: self.clone(),
            structure: ProofBranchStructure::Cases { disjunction },
            split,
            child_goals,
            entries: [arms[0].checkpoint(), arms[1].checkpoint()],
            arms,
        })
    }

    /// Opens a proposition proof under a condition and its exact surface
    /// negation. Unlike `cases`, proof `if` is an audited logical split and
    /// does not require the condition to be an available fact beforehand.
    pub(super) fn begin_if(
        &self,
        condition: ClickProposition,
    ) -> Result<ProofBranches<'a>, ClickError> {
        if self.state.goals.is_discharged() {
            return Err(self.step_error("`if` follows a completed proof"));
        }
        self.proposition_goal("proof `if` requires a proposition goal")?;
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let (split, child_goals, [then_goals, else_goals]) =
            self.state.goals.branch_children::<2>();
        let arms = [
            self.branch_arm(then_fact, then_goals),
            self.branch_arm(else_fact, else_goals),
        ];
        Ok(ProofBranches {
            root: self.clone(),
            structure: ProofBranchStructure::If { condition },
            split,
            child_goals,
            entries: [arms[0].checkpoint(), arms[1].checkpoint()],
            arms,
        })
    }

    /// Partitions an already-checked terminal execution by one proof-level
    /// condition. Every owned outcome must decide exactly one polarity; no
    /// path may be copied into both arms or silently discarded.
    fn begin_execution_outcome_if(
        &self,
        condition: ClickProposition,
    ) -> Result<ExecutionOutcomeProofBranches<'a>, ClickError> {
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
        let (split, child_goals, children_goals) = self.state.goals.branch_children::<2>();
        let mut arms = Vec::with_capacity(2);
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

            let mut facts = self.facts().clone();
            let mut added_facts = Vec::new();
            for fact in std::iter::once(&polarity_facts[arm_index])
                .chain(common_path_facts[arm_index].as_ref().into_iter().flatten())
            {
                if !facts.contains(fact) {
                    facts = facts.with_fact(fact.clone());
                    added_facts.push(fact.clone());
                }
            }
            arms.push(Proof {
                context: self.context.clone(),
                state: Arc::new(ProofState {
                    locals: self.state.locals.clone(),
                    unfolded_predicates: self.state.unfolded_predicates.clone(),
                    goals: children_goals[arm_index].replace_sole_frontier(facts, execution),
                    added_facts: Arc::new(added_facts.clone()),
                    checked_facts: Arc::new(added_facts),
                }),
                // The entry marker records this split instance; the join
                // accepts only descendants that pass through it.
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    depth: self.node.depth,
                }),
            });
        }
        let mut arms = arms.into_iter();
        let then_arm = arms
            .next()
            .expect("the then outcome partition was constructed");
        let else_arm = arms
            .next()
            .expect("the else outcome partition was constructed");
        Ok(ExecutionOutcomeProofBranches {
            root: self.clone(),
            split,
            child_goals,
            entries: [then_arm.checkpoint(), else_arm.checkpoint()],
            condition,
            arms: [then_arm, else_arm],
            root_post_execution_count: root_execution.replay.post_execution_tactics.len(),
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
        match (self.sole_goal(), self.context.as_ref()) {
            (Some(Goal::Proposition(_)), _) => {}
            (Some(Goal::Frontier(_)), ProofContext::Point(_) | ProofContext::Execution(_)) => {}
            _ => {
                return Err(self.step_error("`have` requires a proposition or point context"));
            }
        }
        let kernel = self.lower_surface_goal(&proposition, "`have` proposition")?;
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                unfolded_predicates: self.state.unfolded_predicates.clone(),
                // An execution `have` borrows the current immutable frontier
                // solely as its proposition-lowering/theorem context, shared
                // by identity on the nested goal. The nested goal cannot
                // publish a changed frontier: `join` restores the exact root
                // execution state and exposes only the stated proposition.
                goals: ProofGoals::root(Goal::surface_proposition_in(
                    GoalContext {
                        facts: self.facts().clone(),
                        execution: self.goal_execution().cloned(),
                    },
                    kernel.clone(),
                    proposition.clone(),
                )),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
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
        execution.last_step_delta = ExecutionProofStepDelta::default();
        let introduced_facts = checked.added_facts.clone();
        let body = Proof {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                unfolded_predicates: self.state.unfolded_predicates.clone(),
                goals: self
                    .state
                    .goals
                    .replace_sole_frontier(checked.facts, execution),
                added_facts: Arc::new(checked.added_facts.clone()),
                checked_facts: Arc::new(checked.added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
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
    pub(super) fn begin_execution_branch(&self) -> Result<ExecutionProofBranches<'a>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`branch` requires an execution-frontier proof"));
        };
        if self.state.goals.is_discharged() || !matches!(self.sole_goal(), Some(Goal::Frontier(_)))
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
        if current_state.memory().has_pending_heap_allocation() {
            return Err(self.step_error(
                "checked `branch` cannot yet own an unresolved heap-allocation outcome split",
            ));
        }
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
        let (split, child_goals, children_goals) = self.state.goals.branch_children::<2>();
        let mut entries: [Option<ProofCheckpoint<'a>>; 2] = [None, None];
        let mut arms: [Option<ExecutionProofArm<'a>>; 2] = [None, None];
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
                    "could not retain the checked C branch condition spelling: {message}"
                ))
            })?;
            arm_execution
                .replay
                .surface_propositions
                .record_lowering(&surface_path_fact, &kernel_path_fact)?;
            arm_execution.replay.has_structured_branch_history = true;
            arm_execution.branch_path.push(format!(
                "{} arm of C `if` at statement({statement_index})",
                if take_then { "then" } else { "else" }
            ));
            let mut introduced_facts = PersistentOrderedSet::default();
            for fact in &transition.path_facts {
                introduced_facts.insert(fact.clone());
            }
            let arm_index = usize::from(!take_then);
            let proof = Proof {
                context: self.context.clone(),
                state: Arc::new(ProofState {
                    locals: self.state.locals.clone(),
                    unfolded_predicates: self.state.unfolded_predicates.clone(),
                    goals: children_goals[arm_index]
                        .replace_sole_frontier(transition.pure_facts, arm_execution),
                    added_facts: Arc::new(transition.path_facts.clone()),
                    checked_facts: Arc::new(transition.path_facts.clone()),
                }),
                // The structural certificate is owned by the container and
                // installed atomically by the checked join. The entry marker
                // carries no step; its identity records this split instance.
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    depth: self.node.depth,
                }),
            };
            entries[arm_index] = Some(proof.checkpoint());
            let arm = ExecutionProofArm {
                proof,
                introduced_facts,
                introduced_effect_facts: Vec::new(),
                introduced_function_entry_prerequisites: PersistentOrderedSet::default(),
                introduced_function_entry_derivations: PersistentOrderedSet::default(),
                introduced_unfolded_predicates: PersistentOrderedSet::default(),
                condition_theorem: transition.theorem,
            };
            arms[arm_index] = Some(arm);
        }
        if arms.iter().all(Option::is_none) {
            return Err(self.step_error("`branch` found no feasible C `if` arm"));
        }
        Ok(ExecutionProofBranches {
            root: self.clone(),
            split,
            child_goals,
            entries,
            statement_index,
            continuation_index: source_region.continuation_node,
            continuation_remaining: remaining.map(Arc::new),
            execution_start_state,
            initial_continuation_depth,
            arms,
        })
    }

    /// Independently checks an already-serialized simple certificate.
    ///
    /// This is for explicit source verification and expansion/audit, where
    /// replay is intentional. Smart tactics instead search with `apply_step`
    /// and the structural branch operations directly.
    pub(super) fn check_certificate(
        &self,
        certificate: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        self.check_certificate_with_origin(certificate, None)
    }

    fn check_certificate_with_origin(
        &self,
        certificate: &ProofCertificate,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        enum CheckFrame<'certificate, 'proof> {
            Continue {
                steps: &'certificate [SimpleProofStep],
                next: usize,
            },
            BranchLeft {
                branches: ProofBranches<'proof>,
                right: &'certificate ProofCertificate,
            },
            BranchRight {
                branches: ProofBranches<'proof>,
            },
            Have {
                scope: ProofScope<'proof>,
            },
        }

        let mut proof = self.clone();
        let mut steps = certificate.steps();
        let mut next = 0;
        let mut frames = Vec::new();
        loop {
            if let Some(step) = steps.get(next) {
                next += 1;
                match step {
                    SimpleProofStep::Cases {
                        disjunction,
                        left_proof,
                        right_proof,
                    } => {
                        let branches = proof.begin_cases(disjunction.clone())?;
                        proof = branches.arms[ProofArm::Left.index()].clone();
                        frames.push(CheckFrame::Continue { steps, next });
                        frames.push(CheckFrame::BranchLeft {
                            branches,
                            right: right_proof,
                        });
                        steps = left_proof.steps();
                        next = 0;
                    }
                    SimpleProofStep::If {
                        condition,
                        then_proof,
                        else_proof,
                    } => {
                        let branches = proof.begin_if(condition.clone())?;
                        proof = branches.arms[ProofArm::Left.index()].clone();
                        frames.push(CheckFrame::Continue { steps, next });
                        frames.push(CheckFrame::BranchLeft {
                            branches,
                            right: else_proof,
                        });
                        steps = then_proof.steps();
                        next = 0;
                    }
                    SimpleProofStep::Have {
                        proposition,
                        proof: body,
                    } => {
                        let scope = proof.begin_have(proposition.clone())?;
                        proof = scope.body.clone();
                        frames.push(CheckFrame::Continue { steps, next });
                        frames.push(CheckFrame::Have { scope });
                        steps = body.steps();
                        next = 0;
                    }
                    _ => proof = proof.apply_step_with_origin(step.clone(), origin)?,
                }
                continue;
            }

            let Some(frame) = frames.pop() else {
                return Ok(proof);
            };
            match frame {
                CheckFrame::Continue {
                    steps: continuation,
                    next: continuation_next,
                } => {
                    steps = continuation;
                    next = continuation_next;
                }
                CheckFrame::BranchLeft {
                    mut branches,
                    right,
                } => {
                    branches.arms[ProofArm::Left.index()] = proof;
                    proof = branches.arms[ProofArm::Right.index()].clone();
                    frames.push(CheckFrame::BranchRight { branches });
                    steps = right.steps();
                    next = 0;
                }
                CheckFrame::BranchRight { mut branches } => {
                    branches.arms[ProofArm::Right.index()] = proof;
                    proof = branches.join()?;
                    steps = &[];
                    next = 0;
                }
                CheckFrame::Have { mut scope } => {
                    scope.body = proof;
                    proof = scope.join()?;
                    steps = &[];
                    next = 0;
                }
            }
        }
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

    /// Creates one labeled arm of an audited split: the arm receives its
    /// branch-local fact, its recorded child goal collection, and a fresh
    /// entry marker in provenance. The marker carries no step — arm
    /// certificates still contain only their checked body — but its exact
    /// `Arc` identity records which split instance owns the arm.
    fn branch_arm(&self, fact: Proposition, goals: ProofGoals) -> Self {
        let mut facts = self.facts().clone();
        facts = facts.with_fact(fact.clone());
        Self {
            context: self.context.clone(),
            state: Arc::new(ProofState {
                locals: self.state.locals.clone(),
                unfolded_predicates: self.state.unfolded_predicates.clone(),
                goals: goals.with_sole_facts(facts),
                added_facts: Arc::new(vec![fact.clone()]),
                checked_facts: Arc::new(vec![fact]),
            }),
            // The structural step is retained once at join.
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                depth: self.node.depth,
            }),
        }
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
    /// substitute for an in-scope spelling.
    ///
    /// The ordinary checker may use that index to recognize an exact fact.
    /// Smart theorem selection additionally needs arguments that can be
    /// lowered when the retained `apply` step runs. In particular, a local
    /// that has left scope must be spelled through `at(...)` rather than
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
    /// spelling, but a new goal may not: the same spelling can name facts
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
        names
            .into_iter()
            .filter_map(|name| {
                self.state
                    .locals
                    .values
                    .get(&name)
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
        let goal = match self.sole_goal() {
            Some(Goal::Proposition(goal)) => {
                let kernel = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    std::slice::from_ref(name),
                    &goal.kernel,
                    checked.facts.assumptions(),
                )
                .map_err(|message| self.step_error(message))?;
                match &goal.surface {
                    Some(surface) => {
                        let surface = unfold_structural_invariant_proposition(
                            predicate_environment,
                            surface,
                            std::slice::from_ref(name),
                        )
                        .map_err(|message| self.step_error(message))?;
                        Goal::surface_proposition_in(
                            self.refined_context(checked.facts.clone()),
                            kernel,
                            surface,
                        )
                    }
                    None => {
                        Goal::proposition_in(self.refined_context(checked.facts.clone()), kernel)
                    }
                }
            }
            Some(Goal::Frontier(frontier)) => Goal::Frontier(FrontierGoal {
                selection: frontier.selection,
                context: GoalContext {
                    facts: checked.facts.clone(),
                    execution: frontier.context.execution.clone(),
                },
            }),
            None => return Err(self.step_error("`unfold` requires an open goal")),
        };
        let mut unfolded_predicates = self.state.unfolded_predicates.clone();
        unfolded_predicates.insert(name.clone());
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates,
            goals: self.state.goals.replace_sole(goal),
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
        let mut unfolded_predicates = self.state.unfolded_predicates.clone();
        for name in &checked.added_unfolded_predicates {
            unfolded_predicates.insert(name.clone());
        }
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_function_entry_prerequisites,
            function_entry_derivations: checked.added_function_entry_derivations,
            unfolded_predicates: checked.added_unfolded_predicates,
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates,
            // A nested proposition proof stated at this frontier may also
            // unfold facts: the successor preserves the goal's kind while
            // installing the updated snapshot.
            goals: self
                .state
                .goals
                .replace_sole_execution(checked.facts, execution),
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
        execution.last_step_delta = ExecutionProofStepDelta {
            function_entry_prerequisites: checked.added_certification_facts,
            function_entry_derivations: checked.added_derivations,
            unfolded_predicates: Vec::new(),
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .replace_sole_frontier(checked.facts, execution),
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
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .replace_sole_frontier(checked.facts, execution),
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
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .replace_sole_frontier(checked.facts, execution),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    pub(super) fn into_execution_context(self) -> Result<ProofReplayContext, ClickError> {
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
            replay: execution.replay,
            branch_path: execution.branch_path,
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
    /// checker-owned spellings without re-lowering them.
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
                    SimpleProofStep::Assumption,
                    SimpleProofStep::Normalize,
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
        let atomic = (|| {
            let (
                goal,
                derivation,
                premise_pairs,
                all_premises_replayable,
                point_application_closes_goal,
            ) = self.selected_simp_derivation()?;
            all_premises_replayable
                .then(|| {
                    self.check_typed_atomic_simp_candidate(
                        &goal,
                        &derivation,
                        &premise_pairs,
                        point_application_closes_goal,
                    )
                })
                .flatten()
                .or_else(|| self.try_single_selected_equality_rewrite_closure(&premise_pairs))
                .or_else(|| self.try_selected_predecessor_upper_bound(&goal, &premise_pairs))
                .or_else(|| self.try_selected_disjunction_cases(&premise_pairs))
        })();
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
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
            (ClickProposition::Implies(_, _), Proposition::Implies(_, _)) => {
                match attempt::candidate_outcome(self.apply_step(SimpleProofStep::Intro))? {
                    Some(introduced) => introduced.try_simp_closure(),
                    None => Ok(None),
                }
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

    /// Retains the kernel decision and the exact replayable Surface spellings
    /// selected for its context premises. This is a read-only smart query:
    /// only the later `apply_step` calls may advance the proof.
    fn selected_simp_derivation(
        &self,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
        bool,
    )> {
        let (surface_facts, point_application_closes_goal, premise_anchor) =
            match self.context.as_ref() {
                ProofContext::Pure(context) => {
                    (&context.theorem_context.surface_requirements, false, None)
                }
                ProofContext::Point(context) => (
                    context.surface_propositions,
                    true,
                    context.premise_anchor.as_ref(),
                ),
                ProofContext::Execution(_) => return None,
            };
        let goal = self.goal()?.clone();
        let plan = plan_simp_certificate(&goal, self.facts().assumptions())?;
        let SimpEvidence::Derivation(derivation) = plan else {
            return None;
        };
        let replayable_surface = |kernel: &Proposition| {
            surface_facts.surfaces(kernel).find_map(|surface| {
                let matches_kernel = |candidate: &ClickProposition| {
                    let lowered = self
                        .lower_surface_proposition_direct(candidate, "typed simp premise spelling")
                        .ok()?;
                    (lowered == *kernel || condition_polarity_equivalent(&lowered, kernel))
                        .then_some(())
                };
                if matches_kernel(surface).is_some() {
                    return Some(surface.clone());
                }
                let anchor = premise_anchor?;
                let anchored = surface_with_source_site(surface, anchor).ok()?;
                matches_kernel(&anchored).map(|()| anchored)
            })
        };
        let context_premises = derivation.context_premises();
        let mut all_premises_replayable = true;
        let premise_pairs = context_premises
            .iter()
            .filter_map(|premise| {
                if let Some(surface) = replayable_surface(premise) {
                    return Some((premise.clone(), surface));
                }
                let pair = condition_polarity_spellings(premise)
                    .into_iter()
                    .find_map(|spelling| {
                        let surface = replayable_surface(&spelling);
                        surface.map(|surface| (spelling, surface))
                    });
                if pair.is_none() {
                    all_premises_replayable = false;
                }
                pair
            })
            .collect::<Vec<_>>();
        Some((
            goal,
            derivation,
            premise_pairs,
            all_premises_replayable,
            point_application_closes_goal,
        ))
    }

    /// Handles the first bounded equality-refinement search directly on
    /// `Proof`: each equality explicitly selected by the kernel derivation is
    /// tried as one transactional rewrite of the root, after which an
    /// already-audited direct or typed atomic closer must finish it. Chained
    /// rewrite search remains on the compatibility path.
    fn try_single_selected_equality_rewrite_closure(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        for (kernel, surface) in premise_pairs {
            if !matches!(
                kernel,
                Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
                    | Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true)
            ) {
                continue;
            }
            let Ok(rewritten) = self.apply_step(SimpleProofStep::Rewrite(surface.clone())) else {
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
        }
        None
    }

    /// Searches the structured predecessor proof already expressible through
    /// the checked API. The goal itself fixes the value and upper bound, so
    /// this visits only selected equalities connected to that value and one
    /// exact upper-bound premise; it never tries every partially spellable
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
            let ClickProposition::Or(surface_left, surface_right) = surface else {
                continue;
            };
            let Ok(mut branches) = self.begin_cases(surface.clone()) else {
                continue;
            };
            let branch_surfaces = [surface_left.as_ref(), surface_right.as_ref()];
            let mut complete = true;
            for (index, assumed_surface) in branch_surfaces.into_iter().enumerate() {
                let branch = &branches.arms[index];
                let selected = branch.try_simp_closure().ok().flatten().or_else(|| {
                    let rewritten = branch
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
                branches.arms[index] = selected;
            }
            if complete && let Ok(joined) = branches.join() {
                return Some(joined);
            }
        }
        None
    }

    fn try_typed_atomic_simp_closure(&self) -> Option<Self> {
        let (
            goal,
            derivation,
            premise_pairs,
            all_premises_replayable,
            point_application_closes_goal,
        ) = self.selected_simp_derivation()?;
        if !all_premises_replayable {
            return None;
        }
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
        if !matches!(self.context.as_ref(), ProofContext::Pure(_)) {
            return None;
        }
        let goal = self.goal()?;
        let premise_pairs = surfaces
            .iter()
            .map(|surface| {
                let kernel = self
                    .lower_surface_proposition(surface, "restricted simp premise")
                    .ok()?;
                self.facts()
                    .contains_top_level(&kernel)
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
        self.check_typed_atomic_simp_candidate(goal, derivation, &premise_pairs, false)
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
        let candidate = ProofCertificate::from_proof_tactics(&tactics).ok()?;
        let proof = self.check_certificate(&candidate).ok()?;
        proof.is_complete().then_some(proof)
    }

    /// Runs the linear proposition-script subset already represented by
    /// checked `Proof` transitions.
    ///
    /// Bare `apply` and `simp` remain untrusted search operations: they may
    /// inspect the current proof, but each selected simple step advances only
    /// through `apply_step`. Explicit simple tactics in the same script use
    /// that identical path, so a successful search already owns its complete
    /// expandable derivation rather than reconstructing one afterward.
    pub(super) fn try_linear_smart_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let contains_search = script_contains_linear_search(tactics);
        if !contains_search || tactics.is_empty() {
            return Ok(None);
        }

        // Recognize the complete path before doing any search. `simp` closes
        // the remaining goal and is therefore meaningful only at the end.
        if !linear_script_is_supported(tactics) {
            return Ok(None);
        }

        let mut proof = self.clone();
        for tactic in tactics {
            if proof.is_complete() {
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
                ProofTactic::Have(have) => {
                    let scope = proof.begin_have(have.proposition.clone())?;
                    let selected = match &have.proof {
                        SourceProof::Default
                        | SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => {
                            scope.try_simp_closure()?
                        }
                        SourceProof::Script(body) if script_contains_linear_search(body) => {
                            scope.try_linear_smart_script(body)?
                        }
                        SourceProof::Script(body) => {
                            let Ok(certificate) = ProofCertificate::from_proof_tactics(body) else {
                                return Ok(None);
                            };
                            scope.check_certificate(&certificate).ok()
                        }
                        SourceProof::Tactic(SmartTactic::Frame) => None,
                    };
                    let Some(selected) = selected else {
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let branches = proof.begin_if(proof_if.condition.clone())?;
                    let selected = if script_contains_linear_search(&proof_if.then_tactics) {
                        branches.try_linear_smart_script(ProofArm::Left, &proof_if.then_tactics)?
                    } else {
                        let Ok(certificate) =
                            ProofCertificate::from_proof_tactics(&proof_if.then_tactics)
                        else {
                            return Ok(None);
                        };
                        branches
                            .check_certificate(ProofArm::Left, &certificate)
                            .ok()
                    };
                    let Some(branches) = selected else {
                        return Ok(None);
                    };
                    let selected = if script_contains_linear_search(&proof_if.else_tactics) {
                        branches.try_linear_smart_script(ProofArm::Right, &proof_if.else_tactics)?
                    } else {
                        let Ok(certificate) =
                            ProofCertificate::from_proof_tactics(&proof_if.else_tactics)
                        else {
                            return Ok(None);
                        };
                        branches
                            .check_certificate(ProofArm::Right, &certificate)
                            .ok()
                    };
                    let Some(branches) = selected else {
                        return Ok(None);
                    };
                    proof = branches.join()?;
                }
                ProofTactic::Cases(proof_cases) => {
                    let branches = proof.begin_cases(proof_cases.disjunction.clone())?;
                    let selected = if script_contains_linear_search(&proof_cases.left_tactics) {
                        branches
                            .try_linear_smart_script(ProofArm::Left, &proof_cases.left_tactics)?
                    } else {
                        let Ok(certificate) =
                            ProofCertificate::from_proof_tactics(&proof_cases.left_tactics)
                        else {
                            return Ok(None);
                        };
                        branches
                            .check_certificate(ProofArm::Left, &certificate)
                            .ok()
                    };
                    let Some(branches) = selected else {
                        return Ok(None);
                    };
                    let selected = if script_contains_linear_search(&proof_cases.right_tactics) {
                        branches
                            .try_linear_smart_script(ProofArm::Right, &proof_cases.right_tactics)?
                    } else {
                        let Ok(certificate) =
                            ProofCertificate::from_proof_tactics(&proof_cases.right_tactics)
                        else {
                            return Ok(None);
                        };
                        branches
                            .check_certificate(ProofArm::Right, &certificate)
                            .ok()
                    };
                    let Some(branches) = selected else {
                        return Ok(None);
                    };
                    proof = branches.join()?;
                }
                tactic => {
                    let step = explicit_linear_step(tactic)
                        .expect("the linear script was recognized before execution");
                    proof = proof.apply_step(step)?;
                }
            }
        }

        Ok(proof.is_complete().then_some(proof))
    }

    /// Whether this source proof is a smart script wholly represented by the
    /// recursive proposition driver. This is a syntax-only capability query;
    /// it does not inspect facts, lower propositions, or advance a proof.
    pub(super) fn supports_linear_smart_source(proof: &SourceProof) -> bool {
        source_proof_contains_linear_search(proof) && source_proof_is_supported(proof)
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
        // A standalone `step()` cannot yet decide which resource-backed facts
        // a later tactic will need. Preserve the transactional compatibility
        // boundary until its continuation is searched on this Proof too. An
        // explicit resource scope has an owned continuation contract and uses
        // the broader selector through `ProofScope::try_smart_step` below.
        if !execution.state.resources().facts().is_empty() {
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
    fn try_indexed_execute_step(&self) -> Result<Option<Self>, ClickError> {
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
            for fact in self.state.added_facts.iter() {
                if execution
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
                // Surface proposition spelling. The empty simple candidate
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

    /// Whether the checked execution frontier is a structural C `if`.
    ///
    /// Smart `execute` uses this read-only query to distinguish a structural
    /// frontier from an ordinary statement whose indexed candidate simply did
    /// not apply. It grants no branch authority and performs no transition.
    fn is_at_execution_branch(&self) -> Result<bool, ClickError> {
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
                let branches = proof.begin_execution_branch()?;
                if let Some(take_then) = branches.sole_feasible_arm() {
                    let Some(branches) = branches.try_execute_arm_to_exit(take_then)? else {
                        return Ok(None);
                    };
                    branches.finish_decided()?
                } else {
                    let Some(branches) = branches.try_execute_arm_to_exit(true)? else {
                        return Ok(None);
                    };
                    let Some(branches) = branches.try_execute_arm_to_exit(false)? else {
                        return Ok(None);
                    };
                    branches.join_terminal()?
                }
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

    /// Searches explicit premise spellings for one point fact transport.
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
        if !matches!(self.context.as_ref(), ProofContext::Point(_)) {
            return Err(self.step_error("fact-transport search requires a point proof"));
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
    /// candidate and the source's own explicit spelling; it never scans the
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
            return Err(
                self.step_error("`transport` requires at least one completed execution step")
            );
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
            ProofContext::Execution(_) if !self.is_at_function_exit() => {
                self.select_execution_theorem_application_step(application)
            }
            // A function-exit execution Proof owns several result-sensitive
            // point contexts. Ordered finalization keeps that distinct seam
            // until outcome proposition goals themselves migrate into Proof.
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
            // so sibling snapshot spellings remain visible without rebuilding
            // the complete ambient fact vector. The returned spelling still
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
                    "theorem application `{}` has no checked Click spelling for exact premise `{requirement:?}`",
                    application.name
                )));
            }
            let surface = candidates
                .into_iter()
                // SurfacePropositionMap treats the most recently recorded
                // spelling as canonical. Prefer it here too; earlier entries
                // can be mechanically valid but over-anchor constants as
                // `at(point, constant)` and produce needlessly unstable
                // certificates.
                .rev()
                .find(|candidate| {
                    let matches_requirement = |lowered: &Proposition| {
                        (normalize_direct_atomic_memory_loads(lowered)
                            == normalize_direct_atomic_memory_loads(&requirement)
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
                        "theorem application `{}` has no checked Click spelling for exact premise `{requirement:?}`{}",
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
    /// This instantiates the applied theorem's own requirement spellings and
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
            if normalize_direct_atomic_memory_loads(&lowered)
                != normalize_direct_atomic_memory_loads(&requirement)
                || !self.facts().contains(&lowered)
            {
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
            ProofContext::Point(context) => {
                self.apply_point_theorem_using(context, application, surface_premises)
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
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.with_sole_facts(facts),
            checked_facts: Arc::new(added_facts.clone()),
            added_facts: Arc::new(added_facts),
        })
    }

    fn apply_point_theorem_using(
        &self,
        context: &PointProofContext<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let checked = check_point_theorem_application_using_facts(
            context.theorem_environment,
            application,
            surface_premises,
            context.claim_label,
            context.tactic_index,
            &self.facts(),
            context.parameters,
            context.arguments,
            context.pre_state,
            context.state,
            context.result,
            context.program_point_states,
            context.surface_propositions,
            &unfolded_predicates,
            context.effect_facts,
            context.predicate_environment,
            context.click_function_environment,
            false,
        )?;
        let complete = self.goal().is_some_and(|goal| checked.facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.discharged_if(complete, checked.facts),
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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .discharged_if_or_execution(complete, checked.facts, execution),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
        })
    }

    fn apply_point_choose(&self, choice: &ProofChoice) -> Result<ProofState, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("`choose` requires a point proposition proof"));
        };
        self.proposition_goal("`choose` requires a proposition goal")?;
        if choice.name == "result"
            || context.state.locals().contains_name(&choice.name)
            || self.state.locals.values.contains_key(&choice.name)
        {
            return Err(self.step_error(format!("`{}` is already in scope", choice.name)));
        }

        let source_index = match &choice.source {
            ProofFactSource::Requirement(index) => {
                if *index >= context.original_requirements.len() {
                    return Err(self.step_error(format!(
                        "requirement {index} is out of range; function has {} requirement(s)",
                        context.original_requirements.len()
                    )));
                }
                *index
            }
            ProofFactSource::RequirementLabel(label) => context
                .requirement_label_indices
                .and_then(|indices| indices.get(label))
                .copied()
                .ok_or_else(|| self.step_error(format!("unknown requirement label `{label}`")))?,
        };
        let mut source = context
            .requirement_facts
            .get(source_index)
            .cloned()
            .ok_or_else(|| {
                self.step_error(format!("requirement {source_index} was not available"))
            })?;
        let unfolded_predicates = self.active_unfolded_predicates();
        if !matches!(source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty() {
            source = unfold_predicates_in_proposition(
                context.predicate_environment,
                context.click_function_environment,
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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.with_sole_facts(facts),
            added_facts: Arc::new(added_facts),
            checked_facts: Arc::new(vec![chosen_fact]),
        })
    }

    fn apply_point_witness(&self, witness: &ProofWitness) -> Result<ProofState, ClickError> {
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("`witness` requires a point proposition proof"));
        };
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = unfold_predicates_in_proposition(
            context.predicate_environment,
            context.click_function_environment,
            &unfolded_predicates,
            &goal,
            self.facts().assumptions(),
        )
        .map_err(|message| self.step_error(format!("could not unfold witness goal: {message}")))?;
        let values = parameter_values(context.parameters, context.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs =
            array_refs_for_parameters(context.parameters, &values, context.state.memory());
        let (values, array_refs) =
            contract_environment_at_state(&values, &array_refs, context.state);
        let checked_witness = ProofWitness {
            name: witness.name.clone(),
            value: self.substitute_point_locals_in_expression(&witness.value)?,
        };
        let value = evaluate_witness_tactic_value(
            &checked_witness,
            context.claim_label,
            0,
            context.tactic_index,
            &values,
            &array_refs,
            context.pre_state,
            context.state,
            context.result,
            self.facts().assumptions(),
            context.predicate_environment,
            context.click_function_environment,
            context.program_point_states,
        )?;
        let goal = apply_witness_tactic(
            &checked_witness,
            value,
            goal,
            context.claim_label,
            0,
            context.tactic_index,
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
            _ => None,
        };
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.replace_sole({
                let context = self.refined_context(self.facts().clone());
                surface_goal
                    .map(|surface| {
                        Goal::surface_proposition_in(context.clone(), goal.clone(), surface)
                    })
                    .unwrap_or_else(|| Goal::proposition_in(context, goal))
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
        let ProofContext::Point(context) = self.context.as_ref() else {
            return Err(self.step_error("`instantiate` requires a point proposition proof"));
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

        let parameter_values = parameter_values(context.parameters, context.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            context.parameters,
            &parameter_values,
            context.state.memory(),
        );
        let (values, array_refs) =
            contract_environment_at_state(&parameter_values, &array_refs, context.state);
        let mut active_functions = BTreeSet::new();
        let argument = self.substitute_point_locals_in_expression(argument)?;
        let value = evaluate_contract_expression_with_environment(
            &values,
            &array_refs,
            context.pre_state,
            context.state,
            context.result,
            self.facts().assumptions(),
            &argument,
            context.predicate_environment,
            context.click_function_environment,
            context.program_point_states,
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
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        let added_facts = added.then_some(conclusion).into_iter().collect::<Vec<_>>();
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.discharged_if(complete, facts),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    fn apply_rewrite(&self, surface_equality: &ClickProposition) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.apply_pure_rewrite(surface_equality),
            ProofContext::Point(context) => self.apply_point_rewrite(context, surface_equality),
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

    #[inline(never)]
    fn apply_point_rewrite(
        &self,
        context: &PointProofContext<'_>,
        surface_equality: &ClickProposition,
    ) -> Result<ProofState, ClickError> {
        let goal = Box::new(
            unfold_predicates_in_proposition(
                context.predicate_environment,
                context.click_function_environment,
                context.unfolded_predicates,
                self.proposition_goal("`rewrite` requires a proposition goal")?,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` goal: {message}"))
            })?,
        );
        let recorded = context
            .surface_propositions
            .available_kernel_matching(surface_equality, |kernel| {
                self.facts().materialization_available(kernel)
            })
            .map(|kernel| Box::new(kernel.clone()))
            .or_else(|| {
                let reverse = reverse_surface_equality(surface_equality)?;
                let kernel = context
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
                    self.step_error(format!("could not lower `rewrite` equality: {message}"))
                })?,
            ),
        };
        let equality = Box::new(
            unfold_predicates_in_proposition(
                context.predicate_environment,
                context.click_function_environment,
                context.unfolded_predicates,
                &equality,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` equality: {message}"))
            })?,
        );
        self.finish_rewrite(goal, equality, surface_equality)
    }

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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.replace_sole({
                let context = self.refined_context(self.facts().clone());
                surface_goal
                    .map(|surface| {
                        Goal::surface_proposition_in(context.clone(), rewritten.clone(), surface)
                    })
                    .unwrap_or_else(|| Goal::proposition_in(context, rewritten))
            }),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    fn apply_extract(&self, surface: &ClickProposition) -> Result<ProofState, ClickError> {
        if matches!(self.context.as_ref(), ProofContext::Execution(_)) {
            return Err(self.step_error("`extract` requires a proposition proof"));
        }
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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.discharged_if(complete, facts),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    fn apply_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
        match self.context.as_ref() {
            ProofContext::Point(context) => {
                self.apply_point_transport_using(source, target, premises, context)
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
        context: &PointProofContext<'a>,
    ) -> Result<ProofState, ClickError> {
        let checked = check_point_fact_transport_using_facts(
            source,
            target,
            premises,
            context.claim_label,
            context.tactic_index,
            &self.facts(),
            context.effect_facts,
            context.parameters,
            context.arguments,
            context.pre_state,
            context.state,
            context.result,
            context.program_point_states,
            context.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
        )?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        let checked_facts = vec![checked.source, checked.target.clone()];
        facts = facts.with_fact(checked.target);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.discharged_if(complete, facts),
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
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.replace_sole_execution(facts, execution),
            added_facts: Arc::new(added_facts.clone()),
            checked_facts: Arc::new(added_facts),
        })
    }

    fn apply_execution_statement_using(
        &self,
        premises: &[ClickProposition],
    ) -> Result<ProofState, ClickError> {
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
        Ok(ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .replace_sole_frontier(checked.facts, execution),
            added_facts: Arc::new(checked.added_facts.clone()),
            checked_facts: Arc::new(checked.added_facts),
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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .replace_sole_frontier(self.facts().clone(), execution),
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
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self
                .state
                .goals
                .replace_sole_frontier(self.facts().clone(), execution),
            added_facts: Arc::new(Vec::new()),
            checked_facts: Arc::new(Vec::new()),
        })
    }

    fn apply_contradiction(&self, surface: &ClickProposition) -> Result<ProofState, ClickError> {
        let fact = match self.context.as_ref() {
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
                self.step_error(format!("could not lower `contradiction` fact: {message}"))
            })?,
            ProofContext::Point(context) => {
                if let Some(recorded) = context
                    .surface_propositions
                    .available_kernel(surface, context.lowering_context.as_ref())
                {
                    recorded.clone()
                } else {
                    lower_point_proposition(
                        surface,
                        context.lowering_context.as_ref(),
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
                        self.step_error(format!("could not lower `contradiction` fact: {message}"))
                    })?
                }
            }
            ProofContext::Execution(_) => {
                return Err(self.step_error("`contradiction` requires a proposition goal"));
            }
        };
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
        matches!(self.sole_goal(), Some(Goal::Frontier(_)))
            .then_some(())
            .ok_or_else(|| {
                self.step_error(format!(
                    "{operation} cannot advance C execution inside a proposition proof"
                ))
            })
    }

    fn closed_state(&self) -> ProofState {
        ProofState {
            locals: self.state.locals.clone(),
            unfolded_predicates: self.state.unfolded_predicates.clone(),
            goals: self.state.goals.discharge_sole(),
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

impl<'a> ProofBranches<'a> {
    #[cfg(test)]
    pub(super) fn arm(&self, arm: ProofArm) -> &Proof<'a> {
        &self.arms[arm.index()]
    }

    /// Applies one ordinary checked step inside one arm while preserving the
    /// other arm and the shared root. Failed candidates leave `self` intact.
    #[allow(dead_code)]
    pub(super) fn apply_step(
        &self,
        arm: ProofArm,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.arms[arm.index()] = self.arms[arm.index()].apply_step(step)?;
        Ok(next)
    }

    /// Runs a recognized linear smart script against one branch-local Proof.
    /// The selected descendant retains its exact checked steps; neither the
    /// sibling arm nor the common root is reconstructed or replayed.
    pub(super) fn try_linear_smart_script(
        &self,
        arm: ProofArm,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        let Some(checked) = self.arms[arm.index()].try_linear_smart_script(tactics)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.arms[arm.index()] = checked;
        Ok(Some(next))
    }

    /// Checks one already-simple branch body through the arm's owned Proof.
    /// This supports mixed smart/explicit branches without giving the search
    /// driver a second semantic transition path.
    fn check_certificate(
        &self,
        arm: ProofArm,
        certificate: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.arms[arm.index()] = self.arms[arm.index()].check_certificate(certificate)?;
        Ok(next)
    }

    /// Joins two completed arms and records their retained bodies as one
    /// structured simple step on the shared root.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
        for (index, (name, arm)) in [("left", &self.arms[0]), ("right", &self.arms[1])]
            .into_iter()
            .enumerate()
        {
            if !arm.is_complete() {
                return Err(self
                    .root
                    .step_error(format!("cannot join `cases`: {name} arm is incomplete")));
            }
            // A still-open foreign arm is already rejected as incomplete; a
            // completed arm must additionally descend through this arm's own
            // recorded entry marker, so a proof checked under another split
            // of the same root cannot be spliced into this join.
            if let Some(open) = arm.sole_goal_id()
                && open != self.child_goals[index]
            {
                return Err(self.root.step_error(format!(
                    "cannot join `cases`: {name} arm owns goal {open:?}, not the goal recorded by split {:?}",
                    self.split
                )));
            }
        }
        let left_proof = self.arms[0]
            .certificate_since(&self.entries[0])
            .map_err(|error| {
                self.root.step_error(format!(
                    "cannot join `cases`: left arm did not derive from split {:?} ({error:?})",
                    self.split
                ))
            })?;
        let right_proof = self.arms[1]
            .certificate_since(&self.entries[1])
            .map_err(|error| {
                self.root.step_error(format!(
                    "cannot join `cases`: right arm did not derive from split {:?} ({error:?})",
                    self.split
                ))
            })?;
        let step = match self.structure {
            ProofBranchStructure::Cases { disjunction } => SimpleProofStep::Cases {
                disjunction,
                left_proof: Box::new(left_proof),
                right_proof: Box::new(right_proof),
            },
            ProofBranchStructure::If { condition } => SimpleProofStep::If {
                condition,
                then_proof: Box::new(left_proof),
                else_proof: Box::new(right_proof),
            },
        };
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(self.root.closed_state()),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(step)),
                depth: self.root.node.depth + 1,
            }),
        })
    }
}

impl<'a> ExecutionOutcomeProofBranches<'a> {
    fn check_arm_certificate(
        mut self,
        arm_index: usize,
        certificate: &ProofCertificate,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        self.arms[arm_index] = self.arms[arm_index]
            .apply_contextual_frame_candidate_certificate(certificate, origin)?;
        Ok(self)
    }

    /// Joins two exhaustive terminal outcome partitions after both have
    /// checked the same effect selection. Each arm may retain different
    /// simple evidence, but ordered finalization receives one authority and
    /// therefore performs the resource transition once per original path.
    fn join(self) -> Result<Proof<'a>, ClickError> {
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution outcome branches retained a non-execution context")
        };
        let expected_effects = self.root.selected_effect_indices(context)?;
        for (name, (arm, expected)) in ["then", "else"]
            .into_iter()
            .zip(self.arms.iter().zip(self.child_goals))
        {
            if arm.sole_goal_id() != Some(expected) {
                return Err(self.root.step_error(format!(
                    "execution outcome {name} arm does not own the goal recorded by split {:?}",
                    self.split
                )));
            }
        }
        let arm_certificates = [
            self.arms[0]
                .certificate_since(&self.entries[0])
                .map_err(|error| {
                    self.root.step_error(format!(
                        "execution outcome then arm did not derive from split {:?} ({error:?})",
                        self.split
                    ))
                })?,
            self.arms[1]
                .certificate_since(&self.entries[1])
                .map_err(|error| {
                    self.root.step_error(format!(
                        "execution outcome else arm did not derive from split {:?} ({error:?})",
                        self.split
                    ))
                })?,
        ];
        let mut checked_deferrals = Vec::with_capacity(2);
        for (name, arm) in [("then", &self.arms[0]), ("else", &self.arms[1])] {
            if !matches!(
                arm.sole_goal(),
                Some(Goal::Frontier(FrontierGoal {
                    selection: EffectGoalSelection::None,
                    ..
                }))
            ) {
                return Err(self.root.step_error(format!(
                    "execution outcome {name} arm did not close its effect goal"
                )));
            }
            let execution = arm.execution().ok_or_else(|| {
                self.root.step_error(format!(
                    "execution outcome {name} arm lost its semantic frontier"
                ))
            })?;
            if !execution.replay.is_at_function_exit() {
                return Err(self.root.step_error(format!(
                    "execution outcome {name} arm did not remain at function exit"
                )));
            }
            let mut added = execution
                .replay
                .post_execution_tactics
                .iter()
                .skip(self.root_post_execution_count);
            let deferred = added.next().ok_or_else(|| {
                self.root.step_error(format!(
                    "execution outcome {name} arm retained no checked terminal operation"
                ))
            })?;
            if added.next().is_some() {
                return Err(self.root.step_error(format!(
                    "execution outcome {name} arm retained more than one terminal operation"
                )));
            }
            let PostExecutionTactic::CheckedFrameUsing { authority, .. } = &deferred.tactic else {
                return Err(self.root.step_error(format!(
                    "execution outcome {name} arm did not retain checked frame authority"
                )));
            };
            if authority.effect_indices.as_ref() != &expected_effects {
                return Err(self.root.step_error(format!(
                    "execution outcome {name} arm closed a different effect selection"
                )));
            }
            checked_deferrals.push(deferred.clone());
        }
        if checked_deferrals[0].tactic_index != checked_deferrals[1].tactic_index
            || checked_deferrals[0].source_index != checked_deferrals[1].source_index
        {
            return Err(self.root.step_error(
                "execution outcome arms attribute their frame to different source tactics",
            ));
        }

        let mut execution = self
            .root
            .execution()
            .cloned()
            .expect("validated execution outcome branch root");
        execution.replay.defer_checked_post_execution(
            checked_deferrals[0].tactic_index,
            checked_deferrals[0].source_index,
            PostExecutionTactic::CheckedFrameUsing {
                authority: CheckedFrameAuthority::new(expected_effects),
                // The structured node below owns the two exact surface
                // spellings. This deferral is semantic authority only.
                region: None,
                premises: Vec::new(),
                surface_certificate: None,
            },
        );
        execution.last_step_delta = ExecutionProofStepDelta::default();
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                locals: self.root.state.locals.clone(),
                unfolded_predicates: self.root.state.unfolded_predicates.clone(),
                goals: self
                    .root
                    .state
                    .goals
                    .replace_sole(Goal::Frontier(FrontierGoal {
                        selection: EffectGoalSelection::None,
                        context: GoalContext {
                            facts: self.root.facts().clone(),
                            execution: Some(Arc::new(execution)),
                        },
                    })),
                added_facts: Arc::new(Vec::new()),
                checked_facts: Arc::new(Vec::new()),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::If {
                    condition: self.condition,
                    then_proof: Box::new(arm_certificates[0].clone()),
                    else_proof: Box::new(arm_certificates[1].clone()),
                })),
                depth: self.root.node.depth + 1,
            }),
        })
    }
}

impl<'a> ExecutionProofBranches<'a> {
    /// Extracts one arm's checked body through its recorded entry marker and
    /// requires the arm to still own its recorded child goal. A derivation
    /// from another split of the same root fails here transactionally
    /// instead of being spliced into the structured certificate.
    fn arm_certificate(
        root: &Proof<'a>,
        split: SplitId,
        expected_goal: GoalId,
        entry: Option<&ProofCheckpoint<'a>>,
        arm: &ExecutionProofArm<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        let Some(entry) = entry else {
            return Err(root.step_error(format!(
                "split {split:?} recorded no entry for this branch arm"
            )));
        };
        if arm.proof.sole_goal_id() != Some(expected_goal) {
            return Err(root.step_error(format!(
                "branch arm does not own the goal recorded by split {split:?}"
            )));
        }
        arm.proof.certificate_since(entry).map_err(|error| {
            root.step_error(format!(
                "branch arm did not derive from split {split:?} ({error:?})"
            ))
        })
    }

    fn derived_join_continuation(&self) -> Option<ExecutionBranchJoinContinuation> {
        let root_execution = self.root.execution()?;
        let mut continuations = root_execution.replay.frontier.continuations.clone();
        if let Some(remaining) = &self.continuation_remaining {
            return Some(ExecutionBranchJoinContinuation {
                remaining: remaining.clone(),
                next_statement_index: self.continuation_index,
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

    fn resource_contexts_descend_from_root(&self) -> bool {
        let Some(root_execution) = self.root.execution() else {
            return false;
        };
        let [Some(then_arm), Some(else_arm)] = &self.arms else {
            return false;
        };
        let Some(then_execution) = then_arm.proof.execution() else {
            return false;
        };
        let Some(else_execution) = else_arm.proof.execution() else {
            return false;
        };
        then_execution
            .state
            .resources()
            .descends_from(root_execution.state.resources())
            && else_execution
                .state
                .resources()
                .descends_from(root_execution.state.resources())
    }

    fn common_resources_after_interface_consumption(
        root: &Proof<'a>,
        then_arm: &ExecutionProofArm<'a>,
        else_arm: &ExecutionProofArm<'a>,
        assertions: &[ProofAssertion],
    ) -> Result<ResourceContext, ClickError> {
        let root_execution = root
            .execution()
            .ok_or_else(|| root.step_error("execution branch root lost its resource context"))?;
        let then_execution = then_arm
            .proof
            .execution()
            .ok_or_else(|| root.step_error("then interface arm lost its execution state"))?;
        let else_execution = else_arm
            .proof
            .execution()
            .ok_or_else(|| root.step_error("else interface arm lost its execution state"))?;
        let ProofContext::Execution(context) = root.context.as_ref() else {
            return Err(root.step_error("resource interface requires an execution proof"));
        };
        let mut then_residual = then_execution.state.resources().clone();
        let mut else_residual = else_execution.state.resources().clone();
        for assertion in assertions {
            let ProofAssertion::Resource(resource) = assertion else {
                continue;
            };
            let then_expected = lower_resource_clause_at_state(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &then_execution.state,
            )?;
            if !then_expected.is_own() {
                continue;
            }
            let else_expected = lower_resource_clause_at_state(
                resource,
                context.parsed_function.parameters(),
                context.arguments,
                &else_execution.state,
            )?;
            then_residual = then_residual
                .without_fact_incrementally(
                    &then_expected,
                    then_arm.proof.facts().assumptions(),
                )
                .ok_or_else(|| {
                    root.step_error(
                        "then arm could not consume its established `branch ensuring` ownership representation",
                    )
                })?;
            else_residual = else_residual
                .without_fact_incrementally(
                    &else_expected,
                    else_arm.proof.facts().assumptions(),
                )
                .ok_or_else(|| {
                    root.step_error(
                        "else arm could not consume its established `branch ensuring` ownership representation",
                    )
                })?;
        }
        ResourceContext::common_exact_descendant(
            &then_residual,
            &else_residual,
            root_execution.state.resources(),
        )
        .ok_or_else(|| {
            root.step_error(
                "checked `branch ensuring` resource snapshots do not descend from the branch root",
            )
        })
    }

    fn arm_reached_shared_continuation(&self, arm: &ExecutionProofArm<'a>) -> bool {
        let Some(join) = self.derived_join_continuation() else {
            return false;
        };
        let Some(execution) = arm.proof.execution() else {
            return false;
        };
        execution
            .replay
            .completed_branch_regions
            .contains(&self.statement_index)
            && execution.replay.frontier.next_statement_index == join.next_statement_index
            && execution
                .replay
                .frontier
                .continuations
                .shares_tail_with(&join.continuations)
            && matches!(
                &execution.replay.frontier.point,
                ProofExecutionPoint::StatementEntry { remaining }
                    if remaining.as_ref() == join.remaining.as_ref()
            )
    }

    fn ensure_arm_can_advance(
        &self,
        take_then: bool,
        arm: &ExecutionProofArm<'a>,
    ) -> Result<(), ClickError> {
        if self.arm_reached_shared_continuation(arm) {
            return Err(self.root.step_error(format!(
                "{} arm of `branch` must stop at the shared continuation statement({})",
                if take_then { "then" } else { "else" },
                self.continuation_index
            )));
        }
        Ok(())
    }

    /// Enforces the source `branch` body's boundary without constraining the
    /// separate terminal-execution operation, whose logical certificate may
    /// deliberately continue both arms to function exit.
    pub(super) fn ensure_source_arm_step(
        &self,
        take_then: bool,
        step: &SimpleProofStep,
    ) -> Result<(), ClickError> {
        if !matches!(step, SimpleProofStep::StepUsing(_)) {
            return Ok(());
        }
        let arm = self.arms[usize::from(!take_then)].as_ref().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot advance the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        self.ensure_arm_can_advance(take_then, arm)
    }

    /// Re-derives one logical arm from its retained Surface certificate.
    /// Terminal and decided branches record one synthetic branch-entry
    /// `step using` (two for an empty C arm); those structural entry steps are
    /// validated here and skipped because `begin_execution_branch` already
    /// performed them.
    pub(super) fn check_logical_arm_certificate(
        mut self,
        take_then: bool,
        certificate: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        let root_execution = self.root.execution().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &root_execution.replay,
            &root_execution.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "terminal branch certificate",
        )?;
        let CStatement::If {
            then_branch,
            else_branch,
            ..
        } = statement
        else {
            return Err(self
                .root
                .step_error("terminal branch certificate root is not a C `if`"));
        };
        let source_arm = if take_then {
            then_branch.as_ref()
        } else {
            else_branch.as_ref()
        };
        let entry_steps = 1 + usize::from(matches!(source_arm, CStatement::Skip));
        if certificate.steps().len() < entry_steps
            || !certificate.steps()[..entry_steps]
                .iter()
                .all(|step| matches!(step, SimpleProofStep::StepUsing(_)))
        {
            return Err(self.root.step_error(format!(
                "logical execution {} certificate does not begin with its {entry_steps} checked branch-entry step(s)",
                if take_then { "then" } else { "else" },
            )));
        }
        for step in &certificate.steps()[entry_steps..] {
            self = self.apply_step(take_then, step.clone())?;
        }
        Ok(self)
    }

    fn retain_arm_successor(
        arm: &mut ExecutionProofArm<'a>,
        successor: Proof<'a>,
        prior_effect_count: usize,
    ) {
        arm.proof = successor;
        for fact in arm.proof.added_facts() {
            arm.introduced_facts.insert(fact.clone());
        }
        let execution = arm
            .proof
            .execution()
            .expect("checked execution step retains semantic state");
        for fact in execution
            .replay
            .effect_facts
            .iter()
            .skip(prior_effect_count)
        {
            if !arm.introduced_effect_facts.contains(fact) {
                arm.introduced_effect_facts.push(fact.clone());
            }
        }
        for fact in &execution.last_step_delta.function_entry_prerequisites {
            arm.introduced_function_entry_prerequisites
                .insert(fact.clone());
        }
        for theorem in &execution.last_step_delta.function_entry_derivations {
            arm.introduced_function_entry_derivations
                .insert(theorem.clone());
        }
        for name in &execution.last_step_delta.unfolded_predicates {
            arm.introduced_unfolded_predicates.insert(name.clone());
        }
    }

    fn retain_nested_branch_metadata(
        arm: &mut ExecutionProofArm<'a>,
        nested: &ExecutionProofBranches<'a>,
    ) {
        for nested_arm in nested.arms.iter().flatten() {
            for fact in &nested_arm.introduced_function_entry_prerequisites {
                arm.introduced_function_entry_prerequisites
                    .insert(fact.clone());
            }
            for theorem in &nested_arm.introduced_function_entry_derivations {
                arm.introduced_function_entry_derivations
                    .insert(theorem.clone());
            }
            for name in &nested_arm.introduced_unfolded_predicates {
                arm.introduced_unfolded_predicates.insert(name.clone());
            }
        }
    }

    /// Returns the sole kernel-feasible C arm, or `None` when both arms are
    /// feasible. The no-arm case is rejected when the container is created.
    pub(super) fn sole_feasible_arm(&self) -> Option<bool> {
        match (&self.arms[0], &self.arms[1]) {
            (Some(_), None) => Some(true),
            (None, Some(_)) => Some(false),
            _ => None,
        }
    }

    /// Whether both feasible descendants have completed the C function.
    ///
    /// Search uses this read-only query only to select the audited terminal
    /// join below; it cannot manufacture or edit either outcome.
    pub(super) fn both_arms_at_function_exit(&self) -> bool {
        self.arms.iter().all(|arm| {
            arm.as_ref().is_some_and(|arm| {
                arm.proof
                    .execution()
                    .is_some_and(|execution| execution.replay.is_at_function_exit())
            })
        })
    }

    /// Whether this branch can attempt a checked interface join.
    ///
    /// This structural preflight deliberately does not inspect the exported
    /// interface. Arm steps may establish or fold an owned resource that did
    /// not exist at the branch root. The completed-arm check below decides
    /// whether that resulting representation can actually be joined.
    pub(super) fn supports_interface_branch(&self) -> bool {
        self.sole_feasible_arm().is_some()
            || (self.derived_join_continuation().is_some()
                && self.resource_contexts_descend_from_root())
    }

    #[cfg(test)]
    fn arm(&self, take_then: bool) -> Option<&Proof<'a>> {
        self.arms[usize::from(!take_then)]
            .as_ref()
            .map(|arm| &arm.proof)
    }

    /// Opens one proposition proof rooted at the selected execution arm's
    /// exact current Proof. The nested scope cannot be published into the arm
    /// except through `join_nested`, which checks this ancestry again.
    pub(super) fn begin_have(
        &self,
        take_then: bool,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        let arm = self.arms[usize::from(!take_then)].as_ref().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot begin `have` in the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        arm.proof.begin_have(proposition)
    }

    /// Incorporates one completed proposition scope as the selected arm's
    /// next direct checked successor. A scope searched from another arm or an
    /// earlier arm state cannot be spliced into this container.
    pub(super) fn join_nested(
        &self,
        take_then: bool,
        nested: ProofScope<'a>,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_then);
        let arm = self.arms[arm_index].as_ref().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot join `have` into the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        if !Arc::ptr_eq(&nested.root.context, &arm.proof.context)
            || !Arc::ptr_eq(&nested.root.state, &arm.proof.state)
            || !Arc::ptr_eq(&nested.root.node, &arm.proof.node)
        {
            return Err(self
                .root
                .step_error("nested proof scope is not rooted at the selected execution arm"));
        }
        let prior_effect_count = arm
            .proof
            .execution()
            .ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?
            .replay
            .effect_facts
            .len();
        let successor = nested.join()?;
        let Some(parent) = successor.node.parent.as_ref() else {
            return Err(self
                .root
                .step_error("nested arm proof produced a root without provenance"));
        };
        if !Arc::ptr_eq(parent, &arm.proof.node) {
            return Err(self
                .root
                .step_error("nested arm proof did not produce one direct checked successor"));
        }
        let mut next = self.clone();
        let next_arm = next.arms[arm_index]
            .as_mut()
            .expect("the cloned feasible arm is retained");
        Self::retain_arm_successor(next_arm, successor, prior_effect_count);
        Ok(next)
    }

    /// Applies one checked simple step inside the selected C arm and retains
    /// only that step's semantic fact delta for the eventual join.
    pub(super) fn apply_step(
        mut self,
        take_then: bool,
        step: SimpleProofStep,
    ) -> Result<Self, ClickError> {
        if !matches!(
            step,
            SimpleProofStep::StepUsing(_)
                | SimpleProofStep::TransportUsing { .. }
                | SimpleProofStep::UnfoldPredicate(_)
                | SimpleProofStep::UnfoldResource(_)
                | SimpleProofStep::FoldResource(_)
                | SimpleProofStep::ObserveResource(_)
                | SimpleProofStep::ApplyTheoremUsing { .. }
        ) {
            return Err(self.root.step_error(
                "execution branch arms currently accept only statement, transport, unfold/fold/observe resource, predicate unfold, and theorem-application steps",
            ));
        }
        let arm_index = usize::from(!take_then);
        let mut arm = self.arms[arm_index].take().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot apply a step to the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        let prior_effect_count = arm
            .proof
            .execution()
            .ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?
            .replay
            .effect_facts
            .len();
        let successor = arm.proof.apply_step(step)?;
        Self::retain_arm_successor(&mut arm, successor, prior_effect_count);
        self.arms[arm_index] = Some(arm);
        Ok(self)
    }

    /// Runs one contextual smart statement selector against the selected
    /// arm's owned Proof. Branch arms necessarily carry the root's unrelated
    /// resources and may carry facts introduced by an earlier arm step, so
    /// they use the same indexed selection policy as checked `execute`. A
    /// successful search is already the retained `StepUsing` successor; a
    /// miss leaves this branch container unchanged.
    pub(super) fn try_smart_step(&self, take_then: bool) -> Result<Option<Self>, ClickError> {
        let arm_index = usize::from(!take_then);
        let arm = self.arms[arm_index].as_ref().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot apply a smart step to the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        self.ensure_arm_can_advance(take_then, arm)?;
        let prior_effect_count = arm
            .proof
            .execution()
            .ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?
            .replay
            .effect_facts
            .len();
        let successor = arm.proof.try_indexed_execute_step()?;
        let Some(successor) = successor else {
            return Ok(None);
        };
        let mut next = self.clone();
        let next_arm = next.arms[arm_index]
            .as_mut()
            .expect("the cloned feasible arm is retained");
        Self::retain_arm_successor(next_arm, successor, prior_effect_count);
        Ok(Some(next))
    }

    /// Selects one bare theorem application against the chosen arm's owned
    /// Proof, then submits the resulting explicit `ApplyTheoremUsing` step to
    /// that same Proof. Search cannot add the conclusion directly, and a
    /// failed selection leaves the branch container unchanged.
    pub(super) fn try_theorem_application(
        &self,
        take_then: bool,
        application: &TheoremApplication,
    ) -> Result<Option<Self>, ClickError> {
        let arm_index = usize::from(!take_then);
        let arm = self.arms[arm_index].as_ref().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot apply a theorem to the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        if arm.proof.is_at_function_exit() {
            // Exit applications need one point proof per concrete outcome so
            // that `result` lowers correctly. Ordered finalization owns that
            // distinct operation until outcome goals migrate into Proof.
            return Ok(None);
        }
        let Some(successor) = arm.proof.try_theorem_application(application)? else {
            return Ok(None);
        };
        let prior_effect_count = arm
            .proof
            .execution()
            .ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?
            .replay
            .effect_facts
            .len();
        let mut next = self.clone();
        let next_arm = next.arms[arm_index]
            .as_mut()
            .expect("the cloned feasible arm is retained");
        Self::retain_arm_successor(next_arm, successor, prior_effect_count);
        Ok(Some(next))
    }

    /// Runs bare fact-transport search against the selected arm's immutable
    /// Proof. Each candidate is an explicit `TransportUsing` checked on that
    /// arm; only the already-checked successful descendant is retained.
    pub(super) fn try_fact_transport(
        &self,
        take_then: bool,
        source: &ClickProposition,
        target: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let arm_index = usize::from(!take_then);
        let arm = self.arms[arm_index].as_ref().ok_or_else(|| {
            self.root.step_error(format!(
                "cannot transport a fact in the infeasible {} execution arm",
                if take_then { "then" } else { "else" }
            ))
        })?;
        if arm.proof.is_at_function_exit() {
            return Ok(None);
        }
        let prior_effect_count = arm
            .proof
            .execution()
            .ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?
            .replay
            .effect_facts
            .len();
        let Some(successor) = arm.proof.try_execution_fact_transport(source, target)? else {
            return Ok(None);
        };
        let mut next = self.clone();
        let next_arm = next.arms[arm_index]
            .as_mut()
            .expect("the cloned feasible arm is retained");
        Self::retain_arm_successor(next_arm, successor, prior_effect_count);
        Ok(Some(next))
    }

    /// Runs the narrow statement selector independently in one C arm until
    /// that arm reaches function exit. Every accepted transition is already
    /// a retained `StepUsing` successor. Nested C `if` frontiers recurse
    /// through another checked branch container; any other structural
    /// frontier is a search miss and leaves the caller free to use the legacy
    /// executor.
    pub(super) fn try_execute_arm_to_exit(
        mut self,
        take_then: bool,
    ) -> Result<Option<Self>, ClickError> {
        let arm_index = usize::from(!take_then);
        loop {
            let mut arm = self.arms[arm_index].take().ok_or_else(|| {
                self.root.step_error(format!(
                    "cannot execute the infeasible {} execution arm",
                    if take_then { "then" } else { "else" }
                ))
            })?;
            let execution = arm.proof.execution().ok_or_else(|| {
                self.root
                    .step_error("execution branch arm lost its semantic state")
            })?;
            if execution.replay.is_at_function_exit() {
                self.arms[arm_index] = Some(arm);
                return Ok(Some(self));
            }
            let prior_effect_count = execution.replay.effect_facts.len();
            let successor = if let Some(successor) = arm.proof.try_indexed_execute_step()? {
                successor
            } else {
                if !arm.proof.is_at_execution_branch()? {
                    self.arms[arm_index] = Some(arm);
                    return Ok(None);
                }
                let nested = arm.proof.begin_execution_branch()?;
                if let Some(take_then) = nested.sole_feasible_arm() {
                    let Some(nested) = nested.try_execute_arm_to_exit(take_then)? else {
                        self.arms[arm_index] = Some(arm);
                        return Ok(None);
                    };
                    Self::retain_nested_branch_metadata(&mut arm, &nested);
                    nested.finish_decided()?
                } else {
                    let Some(nested) = nested.try_execute_arm_to_exit(true)? else {
                        self.arms[arm_index] = Some(arm);
                        return Ok(None);
                    };
                    let Some(nested) = nested.try_execute_arm_to_exit(false)? else {
                        self.arms[arm_index] = Some(arm);
                        return Ok(None);
                    };
                    Self::retain_nested_branch_metadata(&mut arm, &nested);
                    nested.join_terminal()?
                }
            };
            Self::retain_arm_successor(&mut arm, successor, prior_effect_count);
            self.arms[arm_index] = Some(arm);
        }
    }

    /// Joins two checked C branch descendants that both return.
    ///
    /// Unlike the equal-state execution `Branch` join, distinct return
    /// outcomes remain as separate paths. The retained certificate is the
    /// logical Surface Click `if` needed to replay those paths: each arm
    /// begins with the explicit statement step(s) whose semantic branch entry
    /// was performed structurally by `begin_execution_branch`.
    pub(super) fn join_terminal(self) -> Result<Proof<'a>, ClickError> {
        let [Some(then_arm), Some(else_arm)] = self.arms else {
            return Err(self
                .root
                .step_error("a terminal execution `branch` requires both feasible arms"));
        };
        if !then_arm
            .proof
            .execution()
            .expect("interface arm retains execution")
            .state
            .resources()
            .shares_storage_with(
                else_arm
                    .proof
                    .execution()
                    .expect("interface arm retains execution")
                    .state
                    .resources(),
            )
        {
            return Err(self.root.step_error(
                "checked `branch ensuring` cannot yet retain a proper common resource delta",
            ));
        }
        let root_execution = self.root.execution().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &root_execution.replay,
            &root_execution.state,
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
            return Err(self
                .root
                .step_error("terminal execution branch root no longer points at a C `if`"));
        };
        let surface_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(self.statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let empty_source_arms = [
            matches!(then_branch.as_ref(), CStatement::Skip),
            matches!(else_branch.as_ref(), CStatement::Skip),
        ];
        let validate_arm = |name: &str,
                            expected: bool,
                            arm: &ExecutionProofArm<'a>|
         -> Result<(), ClickError> {
            let execution = arm.proof.execution().ok_or_else(|| {
                self.root
                    .step_error(format!("{name} branch arm lost its execution state"))
            })?;
            if !execution.replay.is_at_function_exit()
                || execution.replay.frontier.continuations.len() > self.initial_continuation_depth
            {
                return Err(self.root.step_error(format!(
                    "{name} branch arm has not completed at function exit (at exit: {}, continuation depth: {}, root depth: {})",
                    execution.replay.is_at_function_exit(),
                    execution.replay.frontier.continuations.len(),
                    self.initial_continuation_depth,
                )));
            }
            if !matches!(
                implication_body(arm.condition_theorem.proposition()),
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::Value(actual),
                    ..
                } if *actual == expected
            ) {
                return Err(self
                    .root
                    .step_error(format!("{name} arm retained the wrong condition theorem")));
            }
            let replay = &execution.replay;
            if replay.function_entry_execution_prerequisites.len()
                != root_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .len()
                    + arm.introduced_function_entry_prerequisites.len()
                || replay.function_entry_derivations.len()
                    != root_execution.replay.function_entry_derivations.len()
                        + arm.introduced_function_entry_derivations.len()
                || replay.frontier_loop_clauses.len()
                    != root_execution.replay.frontier_loop_clauses.len()
                || replay.frontier_loop_rules.len()
                    != root_execution.replay.frontier_loop_rules.len()
                || replay.unfolded_predicates.len()
                    != root_execution.replay.unfolded_predicates.len()
                        + arm.introduced_unfolded_predicates.len()
                || replay.planned_statement_transitions.len()
                    != root_execution.replay.planned_statement_transitions.len()
            {
                return Err(self.root.step_error(format!(
                        "{name} execution arm changed replay metadata that the checked terminal join has not migrated"
                    )));
            }
            Ok(())
        };
        validate_arm("then", true, &then_arm)?;
        validate_arm("else", false, &else_arm)?;

        let terminal_certificate =
            |arm_index: usize,
             arm: &ExecutionProofArm<'a>,
             empty_source_arm: bool,
             path_condition: ClickProposition| {
                let body = Self::arm_certificate(
                    &self.root,
                    self.split,
                    self.child_goals[arm_index],
                    self.entries[arm_index].as_ref(),
                    arm,
                )?;
                let entry_steps = 1 + usize::from(empty_source_arm);
                let mut steps = Vec::with_capacity(entry_steps + body.steps().len());
                steps.push(SimpleProofStep::StepUsing(vec![path_condition]));
                steps.resize_with(entry_steps, || SimpleProofStep::StepUsing(Vec::new()));
                steps.extend_from_slice(body.steps());
                Ok::<_, ClickError>(ProofCertificate::from_steps(steps))
            };
        let then_proof = terminal_certificate(
            0,
            &then_arm,
            empty_source_arms[0],
            surface_condition.clone(),
        )?;
        let else_proof = terminal_certificate(
            1,
            &else_arm,
            empty_source_arms[1],
            negate_click_proposition(&surface_condition),
        )?;
        let then_execution = then_arm
            .proof
            .execution()
            .expect("validated then execution state");
        let else_execution = else_arm
            .proof
            .execution()
            .expect("validated else execution state");
        let common_program_points = then_execution
            .replay
            .program_point_states
            .common_descendant(
                &else_execution.replay.program_point_states,
                &root_execution.replay.program_point_states,
            )
            .ok_or_else(|| {
                self.root.step_error(
                    "terminal execution arms do not descend from the branch root's program points",
                )
            })?;

        // Root facts remain shared in `ProofState`. Only facts introduced in
        // one arm need to be copied into that arm's returned execution paths;
        // doing so avoids duplicating the complete ambient proof context per
        // outcome.
        let mut paths = Vec::new();
        for arm in [&then_arm, &else_arm] {
            let arm_execution = arm
                .proof
                .execution()
                .expect("validated terminal arm execution");
            let completed = arm_execution
                .replay
                .execution()
                .expect("validated terminal arm is at function exit");
            for path in completed.paths() {
                let mut facts = path.execution_facts();
                for proposition in &arm.introduced_facts {
                    let fact = ExecutionPureFact::new(proposition.clone());
                    if !facts.contains(&fact) {
                        facts.push(fact);
                    }
                }
                let obligations = path.obligations().to_vec();
                if !paths
                    .iter()
                    .any(|(existing_outcome, existing_facts, existing_obligations)| {
                        existing_outcome == path.outcome()
                            && existing_facts == &facts
                            && existing_obligations == &obligations
                    })
                {
                    paths.push((path.outcome().clone(), facts, obligations));
                }
            }
        }

        let outcomes = c_function_execution_candidates_from_outcomes(
            self.execution_start_state.clone(),
            context.function.clone(),
            context.arguments.to_vec(),
            paths,
        );
        let mut execution = root_execution.clone();
        execution.state = self.execution_start_state.clone().into();
        execution.replay.program_point_states = common_program_points;
        execution
            .replay
            .completed_branch_regions
            .insert(self.statement_index);
        for continuation in &root_execution.replay.frontier.continuations {
            if let ProofExecutionContinuationKind::Branch { statement_index } = continuation.kind {
                execution
                    .replay
                    .completed_branch_regions
                    .insert(statement_index);
            }
        }
        execution.replay.frontier.continuations.clear();
        execution.replay.frontier.execution_start_state = Some(self.execution_start_state.clone());
        execution.replay.frontier.point = ProofExecutionPoint::FunctionExit {
            execution: outcomes,
        };
        execution.replay.has_structured_branch_history = true;
        execution.replay.next_opaque_call = then_execution
            .replay
            .next_opaque_call
            .max(else_execution.replay.next_opaque_call);
        execution.replay.next_verification_variable = then_execution
            .replay
            .next_verification_variable
            .max(else_execution.replay.next_verification_variable);
        for effect in then_arm
            .introduced_effect_facts
            .iter()
            .chain(&else_arm.introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in then_arm
            .introduced_function_entry_prerequisites
            .iter()
            .chain(&else_arm.introduced_function_entry_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in then_arm
            .introduced_function_entry_derivations
            .iter()
            .chain(&else_arm.introduced_function_entry_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in then_arm
            .introduced_unfolded_predicates
            .iter()
            .chain(&else_arm.introduced_unfolded_predicates)
        {
            if !execution.replay.unfolded_predicates.contains(name) {
                execution.replay.unfolded_predicates.push(name.clone());
            }
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path = root_execution.branch_path.clone();
        execution.replay.case_assumptions = root_execution.replay.case_assumptions.clone();

        let mut facts = self.root.facts().clone();
        let mut common_added_facts = Vec::new();
        for fact in &then_arm.introduced_facts {
            if else_arm.introduced_facts.contains(fact)
                && then_arm.proof.facts().contains(fact)
                && else_arm.proof.facts().contains(fact)
                && !facts.contains(fact)
            {
                facts = facts.with_fact(fact.clone());
                common_added_facts.push(fact.clone());
                for surface in then_execution.replay.surface_propositions.surfaces(fact) {
                    if else_execution
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
            }
        }
        let mut unfolded_predicates = self.root.state.unfolded_predicates.clone();
        for name in then_arm
            .introduced_unfolded_predicates
            .iter()
            .chain(&else_arm.introduced_unfolded_predicates)
        {
            unfolded_predicates.insert(name.clone());
        }
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                locals: self.root.state.locals.clone(),
                unfolded_predicates,
                goals: self
                    .root
                    .state
                    .goals
                    .replace_sole_frontier(facts, execution),
                added_facts: Arc::new(common_added_facts.clone()),
                checked_facts: Arc::new(common_added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::If {
                    condition: surface_condition,
                    then_proof: Box::new(then_proof),
                    else_proof: Box::new(else_proof),
                })),
                depth: self.root.node.depth + 1,
            }),
        })
    }

    /// Closes a C branch for which the kernel certified exactly one feasible
    /// arm. This is path retention, not a two-state join: the surviving
    /// descendant becomes the successor while a logical `If` records the
    /// checked source condition and an empty contradictory arm.
    pub(super) fn finish_decided(self) -> Result<Proof<'a>, ClickError> {
        let take_then = self.sole_feasible_arm().ok_or_else(|| {
            self.root
                .step_error("a decided execution branch requires exactly one kernel-feasible arm")
        })?;
        let arm_index = usize::from(!take_then);
        let arm = self.arms[arm_index]
            .as_ref()
            .expect("sole feasible arm was selected above");
        let root_execution = self.root.execution().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        let execution = arm.proof.execution().ok_or_else(|| {
            self.root
                .step_error("decided execution branch arm lost its semantic state")
        })?;
        let reached_continuation = execution
            .replay
            .completed_branch_regions
            .contains(&self.statement_index)
            && execution.replay.frontier.continuations.len() <= self.initial_continuation_depth
            && execution.replay.frontier.next_statement_index == self.continuation_index;
        let reached_exit = execution.replay.is_at_function_exit()
            && execution.replay.frontier.continuations.len() <= self.initial_continuation_depth;
        if !reached_continuation && !reached_exit {
            return Err(self.root.step_error(format!(
                "the sole feasible {} execution arm has not reached its continuation or function exit",
                if take_then { "then" } else { "else" }
            )));
        }
        if !matches!(
            implication_body(arm.condition_theorem.proposition()),
            Proposition::CConditionEvaluates {
                outcome: CConditionOutcome::Value(actual),
                ..
            } if *actual == take_then
        ) {
            return Err(self
                .root
                .step_error("the decided execution arm retained the wrong condition theorem"));
        }
        let replay = &execution.replay;
        if replay.function_entry_execution_prerequisites.len()
            != root_execution
                .replay
                .function_entry_execution_prerequisites
                .len()
                + arm.introduced_function_entry_prerequisites.len()
            || replay.function_entry_derivations.len()
                != root_execution.replay.function_entry_derivations.len()
                    + arm.introduced_function_entry_derivations.len()
            || replay.frontier_loop_clauses.len()
                != root_execution.replay.frontier_loop_clauses.len()
            || replay.frontier_loop_rules.len() != root_execution.replay.frontier_loop_rules.len()
            || replay.unfolded_predicates.len()
                != root_execution.replay.unfolded_predicates.len()
                    + arm.introduced_unfolded_predicates.len()
            || replay.planned_statement_transitions.len()
                != root_execution.replay.planned_statement_transitions.len()
        {
            return Err(self.root.step_error(
                "the decided execution arm changed replay metadata that the checked path operation has not migrated",
            ));
        }

        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let (_, _, statement, _) = next_top_level_statement_from_execution_point(
            &root_execution.replay,
            &root_execution.state,
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
            return Err(self
                .root
                .step_error("decided execution branch root no longer points at a C `if`"));
        };
        let surface_condition = surface_with_source_site(
            &surface_c_condition(&condition),
            &ProgramPointRef {
                region: CodeRegionRef::Statement(self.statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let source_arm = if take_then {
            then_branch.as_ref()
        } else {
            else_branch.as_ref()
        };
        let body = Self::arm_certificate(
            &self.root,
            self.split,
            self.child_goals[arm_index],
            self.entries[arm_index].as_ref(),
            arm,
        )?;
        let entry_steps = 1 + usize::from(matches!(source_arm, CStatement::Skip));
        let path_condition = if take_then {
            surface_condition.clone()
        } else {
            negate_click_proposition(&surface_condition)
        };
        let mut selected_steps = Vec::with_capacity(entry_steps + body.steps().len());
        selected_steps.push(SimpleProofStep::StepUsing(vec![path_condition]));
        selected_steps.resize_with(entry_steps, || SimpleProofStep::StepUsing(Vec::new()));
        selected_steps.extend_from_slice(body.steps());
        let selected = ProofCertificate::from_steps(selected_steps);
        let empty = ProofCertificate::from_steps(Vec::new());
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };

        let mut state = (*arm.proof.state).clone();
        let introduced_facts = arm.introduced_facts.to_vec();
        state.added_facts = Arc::new(introduced_facts.clone());
        state.checked_facts = Arc::new(introduced_facts);
        let mut execution = arm
            .proof
            .execution()
            .cloned()
            .expect("validated decided execution state");
        execution.branch_path = root_execution.branch_path.clone();
        let arm_facts = arm.proof.facts().clone();
        state.goals = state.goals.replace_sole_frontier(arm_facts, execution);
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(state),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::If {
                    condition: surface_condition,
                    then_proof: Box::new(then_proof),
                    else_proof: Box::new(else_proof),
                })),
                depth: self.root.node.depth + 1,
            }),
        })
    }

    /// Joins two checked C branch descendants through one explicit common
    /// frontier interface.
    ///
    /// Each arm is independently checked and abstracted before any result is
    /// selected. The operation accepts the join only when those abstract
    /// semantic states and exported facts agree exactly, then records the
    /// corresponding `Branch { ensuring, .. }` certificate atomically.
    pub(super) fn join_with_interface(
        self,
        assertions: Vec<ProofAssertion>,
    ) -> Result<Proof<'a>, ClickError> {
        if self.sole_feasible_arm().is_some() {
            return self.finish_decided_with_interface(assertions);
        }
        let join_continuation = self.derived_join_continuation().ok_or_else(|| {
            self.root
                .step_error("execution `branch` has no shared continuation statement")
        })?;
        let [Some(then_arm), Some(else_arm)] = self.arms else {
            return Err(self
                .root
                .step_error("checked `branch ensuring` found no feasible continuing arm"));
        };
        let root_execution = self.root.execution().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        let validate_arm = |name: &str,
                            expected: bool,
                            arm: &ExecutionProofArm<'a>|
         -> Result<(), ClickError> {
            let execution = arm.proof.execution().ok_or_else(|| {
                self.root
                    .step_error(format!("{name} branch arm lost its execution state"))
            })?;
            if !execution
                .replay
                .completed_branch_regions
                .contains(&self.statement_index)
                || join_continuation
                    .completed_enclosing_branches
                    .iter()
                    .any(|statement_index| {
                        !execution
                            .replay
                            .completed_branch_regions
                            .contains(statement_index)
                    })
                || !execution
                    .replay
                    .frontier
                    .continuations
                    .shares_tail_with(&join_continuation.continuations)
                || execution.replay.frontier.next_statement_index
                    != join_continuation.next_statement_index
                || !matches!(
                    &execution.replay.frontier.point,
                    ProofExecutionPoint::StatementEntry { remaining }
                        if remaining.as_ref() == join_continuation.remaining.as_ref()
                )
                || execution.replay.is_at_function_exit()
            {
                return Err(self.root.step_error(format!(
                    "{name} `branch ensuring` arm has not reached its shared continuation"
                )));
            }
            if !matches!(
                implication_body(arm.condition_theorem.proposition()),
                Proposition::CConditionEvaluates {
                    outcome: CConditionOutcome::Value(actual),
                    ..
                } if *actual == expected
            ) {
                return Err(self
                    .root
                    .step_error(format!("{name} arm retained the wrong condition theorem")));
            }
            let replay = &execution.replay;
            if replay.function_entry_execution_prerequisites.len()
                != root_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .len()
                    + arm.introduced_function_entry_prerequisites.len()
                || replay.function_entry_derivations.len()
                    != root_execution.replay.function_entry_derivations.len()
                        + arm.introduced_function_entry_derivations.len()
                || replay.frontier_loop_clauses.len()
                    != root_execution.replay.frontier_loop_clauses.len()
                || replay.frontier_loop_rules.len()
                    != root_execution.replay.frontier_loop_rules.len()
                || replay.unfolded_predicates.len()
                    != root_execution.replay.unfolded_predicates.len()
                        + arm.introduced_unfolded_predicates.len()
                || replay.planned_statement_transitions.len()
                    != root_execution.replay.planned_statement_transitions.len()
            {
                return Err(self.root.step_error(format!(
                        "{name} execution arm changed replay metadata that the checked interface join has not migrated"
                    )));
            }
            Ok(())
        };
        validate_arm("then", true, &then_arm)?;
        validate_arm("else", false, &else_arm)?;

        let then_proof = Self::arm_certificate(
            &self.root,
            self.split,
            self.child_goals[0],
            self.entries[0].as_ref(),
            &then_arm,
        )?;
        let else_proof = Self::arm_certificate(
            &self.root,
            self.split,
            self.child_goals[1],
            self.entries[1].as_ref(),
            &else_arm,
        )?;
        let then_execution = then_arm
            .proof
            .execution()
            .expect("validated then execution state");
        let else_execution = else_arm
            .proof
            .execution()
            .expect("validated else execution state");
        let common_program_points = then_execution
            .replay
            .program_point_states
            .common_descendant(
                &else_execution.replay.program_point_states,
                &root_execution.replay.program_point_states,
            )
            .ok_or_else(|| {
                self.root.step_error(
                    "`branch ensuring` arms do not descend from the root program-point state",
                )
            })?;

        let mut stable_join_locals = then_execution
            .state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        stable_join_locals
            .retain(|name, value| else_execution.state.locals().get(name) == Some(value));
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(join_continuation.next_statement_index),
            kind: ProgramPointKind::Entry,
        };

        let abstract_arm =
            |arm: &ExecutionProofArm<'a>| -> Result<(ExecutionProofState, ProofFacts), ClickError> {
                let mut execution = arm
                    .proof
                    .execution()
                    .expect("validated interface arm execution")
                    .clone();
                let mut facts = arm.proof.facts().clone();
                let mut state = (*execution.state).clone();
                let ProofContext::Execution(context) = self.root.context.as_ref() else {
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
                    true,
                )
                .map_err(|error| add_proof_branch_path(error, &execution.branch_path))?;
                execution.state = state.into();
                Ok((execution, facts))
            };
        let (mut then_abstract, then_interface_facts) = abstract_arm(&then_arm)?;
        let (else_abstract, else_interface_facts) = abstract_arm(&else_arm)?;

        let then_interface_vec = then_interface_facts.to_vec();
        let else_interface_vec = else_interface_facts.to_vec();
        if then_interface_vec != else_interface_vec || *then_abstract.state != *else_abstract.state
        {
            return Err(self.root.step_error(
                "`branch ensuring` arms produced different abstract successor states",
            ));
        }

        // Consume owned exports from both concrete arms before intersecting
        // their exact residuals. Re-adding the normalized interface below
        // therefore neither duplicates a common representation nor loses the
        // portion of ownership selected by the interface.
        let common_resources = Self::common_resources_after_interface_consumption(
            &self.root,
            &then_arm,
            &else_arm,
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
                self.root.step_error(format!(
                    "invalid automatic common `branch ensuring` resource interface: {error:?}"
                ))
            })?
            .normalized_around_facts(&additions, then_interface_facts.assumptions());
        let state = (*then_abstract.state)
            .clone()
            .with_resource_context(resources);
        then_abstract.state = state.into();

        let abstract_state = (*then_abstract.state).clone();
        let mut execution = root_execution.clone();
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
            .insert(self.statement_index);
        for statement_index in &join_continuation.completed_enclosing_branches {
            execution
                .replay
                .completed_branch_regions
                .insert(*statement_index);
        }
        execution.replay.frontier.next_statement_index = join_continuation.next_statement_index;
        execution.replay.frontier.continuations = join_continuation.continuations;
        execution.replay.frontier.execution_start_state = Some(self.execution_start_state);
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
        execution.replay.next_verification_variable = then_abstract
            .replay
            .next_verification_variable
            .max(else_abstract.replay.next_verification_variable);
        for effect in then_arm
            .introduced_effect_facts
            .iter()
            .chain(&else_arm.introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in then_arm
            .introduced_function_entry_prerequisites
            .iter()
            .chain(&else_arm.introduced_function_entry_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in then_arm
            .introduced_function_entry_derivations
            .iter()
            .chain(&else_arm.introduced_function_entry_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path.clear();
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_point_state(
            &mut execution.replay,
            context.function_block,
            self.statement_index,
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

        let mut facts = self.root.facts().clone();
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
        for fact in &then_arm.introduced_facts {
            if else_arm.introduced_facts.contains(fact)
                && then_arm.proof.facts().contains(fact)
                && else_arm.proof.facts().contains(fact)
            {
                retain_fact(fact)?;
            }
        }

        #[cfg(test)]
        CHECKED_EXECUTION_INTERFACE_JOINS.with(|count| count.set(count.get() + 1));

        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                locals: self.root.state.locals.clone(),
                unfolded_predicates: self.root.state.unfolded_predicates.clone(),
                goals: self
                    .root
                    .state
                    .goals
                    .replace_sole_frontier(facts, execution),
                added_facts: Arc::new(added_facts.clone()),
                checked_facts: Arc::new(added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::Branch {
                    ensuring: Some(assertions),
                    then_proof: Box::new(then_proof),
                    else_proof: Box::new(else_proof),
                })),
                depth: self.root.node.depth + 1,
            }),
        })
    }

    /// Validates an explicit interface on the sole kernel-feasible arm.
    ///
    /// No abstraction or resource merge occurs: the surviving checked state
    /// remains the successor, and the structured `Branch` records an empty
    /// impossible arm. Consequently ownership assertions are safe here even
    /// though two-arm ownership normalization has not migrated.
    fn finish_decided_with_interface(
        self,
        assertions: Vec<ProofAssertion>,
    ) -> Result<Proof<'a>, ClickError> {
        let take_then = self.sole_feasible_arm().ok_or_else(|| {
            self.root
                .step_error("a decided `branch ensuring` requires exactly one kernel-feasible arm")
        })?;
        let arm = self.arms[usize::from(!take_then)]
            .as_ref()
            .expect("sole feasible interface arm was selected");
        let root_execution = self.root.execution().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        let arm_execution = arm.proof.execution().ok_or_else(|| {
            self.root
                .step_error("decided interface arm lost its execution state")
        })?;
        let reached_continuation = arm_execution
            .replay
            .completed_branch_regions
            .contains(&self.statement_index)
            && arm_execution.replay.frontier.continuations.len() <= self.initial_continuation_depth
            && arm_execution.replay.frontier.next_statement_index == self.continuation_index;
        let reached_exit = arm_execution.replay.is_at_function_exit()
            && arm_execution.replay.frontier.continuations.len() <= self.initial_continuation_depth;
        if !reached_continuation && !reached_exit {
            return Err(self.root.step_error(format!(
                "the sole feasible {} `branch ensuring` arm has not reached its continuation or function exit",
                if take_then { "then" } else { "else" }
            )));
        }
        if !matches!(
            implication_body(arm.condition_theorem.proposition()),
            Proposition::CConditionEvaluates {
                outcome: CConditionOutcome::Value(actual),
                ..
            } if *actual == take_then
        ) {
            return Err(self
                .root
                .step_error("the decided interface arm retained the wrong condition theorem"));
        }
        let replay = &arm_execution.replay;
        if replay.function_entry_execution_prerequisites.len()
            != root_execution
                .replay
                .function_entry_execution_prerequisites
                .len()
                + arm.introduced_function_entry_prerequisites.len()
            || replay.function_entry_derivations.len()
                != root_execution.replay.function_entry_derivations.len()
                    + arm.introduced_function_entry_derivations.len()
            || replay.frontier_loop_clauses.len()
                != root_execution.replay.frontier_loop_clauses.len()
            || replay.frontier_loop_rules.len() != root_execution.replay.frontier_loop_rules.len()
            || replay.unfolded_predicates.len()
                != root_execution.replay.unfolded_predicates.len()
                    + arm.introduced_unfolded_predicates.len()
            || replay.planned_statement_transitions.len()
                != root_execution.replay.planned_statement_transitions.len()
        {
            return Err(self.root.step_error(
                "the decided interface arm changed replay metadata that the checked path operation has not migrated",
            ));
        }

        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        let target = ProgramPointRef {
            region: CodeRegionRef::Statement(self.continuation_index),
            kind: ProgramPointKind::Entry,
        };
        let mut execution = arm_execution.clone();
        let mut state = (*execution.state).clone();
        let mut facts = arm.proof.facts().clone();
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
            false,
        )
        .map_err(|error| add_proof_branch_path(error, &execution.branch_path))?;
        execution.state = state.into();
        execution.branch_path = root_execution.branch_path.clone();
        execution.replay.case_assumptions = root_execution.replay.case_assumptions.clone();

        let mut added_facts = arm.introduced_facts.to_vec();
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
        let decided_index = usize::from(!take_then);
        let selected = Self::arm_certificate(
            &self.root,
            self.split,
            self.child_goals[decided_index],
            self.entries[decided_index].as_ref(),
            arm,
        )?;
        let empty = ProofCertificate::from_steps(Vec::new());
        let (then_proof, else_proof) = if take_then {
            (selected, empty)
        } else {
            (empty, selected)
        };
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                locals: arm.proof.state.locals.clone(),
                unfolded_predicates: arm.proof.state.unfolded_predicates.clone(),
                goals: arm
                    .proof
                    .state
                    .goals
                    .replace_sole_frontier(facts, execution),
                added_facts: Arc::new(added_facts.clone()),
                checked_facts: Arc::new(added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(SimpleProofStep::Branch {
                    ensuring: Some(assertions),
                    then_proof: Box::new(then_proof),
                    else_proof: Box::new(else_proof),
                })),
                depth: self.root.node.depth + 1,
            }),
        })
    }

    /// Preserves the original empty-arm entry point for callers that require
    /// the branch to contain no body steps.
    pub(super) fn join_empty(self) -> Result<Proof<'a>, ClickError> {
        self.join_checked(true)
    }

    /// Joins two checked non-returning C branch arms at their shared frontier.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
        self.join_checked(false)
    }

    fn join_checked(self, require_empty: bool) -> Result<Proof<'a>, ClickError> {
        let [Some(then_arm), Some(else_arm)] = self.arms else {
            return Err(self.root.step_error(
                "an execution `branch` with one feasible arm is a decided path, not a join",
            ));
        };
        let validate_arm =
            |name: &str, expected: bool, arm: &ExecutionProofArm<'a>| -> Result<(), ClickError> {
                let arm_index = usize::from(!expected);
                let body = Self::arm_certificate(
                    &self.root,
                    self.split,
                    self.child_goals[arm_index],
                    self.entries[arm_index].as_ref(),
                    arm,
                )?;
                if require_empty && !body.steps().is_empty() {
                    return Err(self.root.step_error(format!(
                        "cannot use the empty execution join for a nonempty {name} arm"
                    )));
                }
                let execution = arm.proof.execution().ok_or_else(|| {
                    self.root
                        .step_error(format!("{name} branch arm lost its execution state"))
                })?;
                if !execution
                    .replay
                    .completed_branch_regions
                    .contains(&self.statement_index)
                    || execution.replay.frontier.continuations.len()
                        > self.initial_continuation_depth
                    || execution.replay.frontier.next_statement_index != self.continuation_index
                {
                    return Err(self.root.step_error(format!(
                        "{name} branch arm has not reached its shared continuation"
                    )));
                }
                if !matches!(
                    implication_body(arm.condition_theorem.proposition()),
                    Proposition::CConditionEvaluates {
                        outcome: CConditionOutcome::Value(actual),
                        ..
                    } if *actual == expected
                ) {
                    return Err(self
                        .root
                        .step_error(format!("{name} arm retained the wrong condition theorem")));
                }
                Ok(())
            };
        validate_arm("then", true, &then_arm)?;
        validate_arm("else", false, &else_arm)?;
        let then_proof = Self::arm_certificate(
            &self.root,
            self.split,
            self.child_goals[0],
            self.entries[0].as_ref(),
            &then_arm,
        )?;
        let else_proof = Self::arm_certificate(
            &self.root,
            self.split,
            self.child_goals[1],
            self.entries[1].as_ref(),
            &else_arm,
        )?;
        let then_state = &then_arm
            .proof
            .execution()
            .expect("validated then execution state")
            .state;
        let else_state = &else_arm
            .proof
            .execution()
            .expect("validated else execution state")
            .state;
        if **then_state != **else_state {
            return Err(self
                .root
                .step_error("execution `branch` arms reached different C states"));
        }
        let continuation_remaining = self.continuation_remaining.ok_or_else(|| {
            self.root
                .step_error("execution `branch` has no shared continuation statement")
        })?;
        let root_execution = self.root.execution().ok_or_else(|| {
            self.root
                .step_error("execution branch root lost its semantic state")
        })?;
        for (name, arm) in [("then", &then_arm), ("else", &else_arm)] {
            let replay = &arm
                .proof
                .execution()
                .expect("validated branch execution state")
                .replay;
            if replay.function_entry_execution_prerequisites.len()
                != root_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .len()
                    + arm.introduced_function_entry_prerequisites.len()
                || replay.function_entry_derivations.len()
                    != root_execution.replay.function_entry_derivations.len()
                        + arm.introduced_function_entry_derivations.len()
                || replay.frontier_loop_clauses.len()
                    != root_execution.replay.frontier_loop_clauses.len()
                || replay.frontier_loop_rules.len()
                    != root_execution.replay.frontier_loop_rules.len()
                || replay.unfolded_predicates.len()
                    != root_execution.replay.unfolded_predicates.len()
                        + arm.introduced_unfolded_predicates.len()
                || replay.planned_statement_transitions.len()
                    != root_execution.replay.planned_statement_transitions.len()
            {
                return Err(self.root.step_error(format!(
                    "{name} execution arm changed replay metadata that the checked join has not migrated"
                )));
            }
        }
        let then_replay = &then_arm
            .proof
            .execution()
            .expect("validated then execution state")
            .replay;
        let else_replay = &else_arm
            .proof
            .execution()
            .expect("validated else execution state")
            .replay;
        let mut execution = root_execution.clone();
        execution.state = (**then_state).clone().into();
        execution.replay.completed_branch_regions.clear();
        execution
            .replay
            .completed_branch_regions
            .insert(self.statement_index);
        execution.replay.frontier.next_statement_index = self.continuation_index;
        execution.replay.frontier.execution_start_state = Some(self.execution_start_state);
        execution.replay.frontier.point = ProofExecutionPoint::StatementEntry {
            remaining: continuation_remaining,
        };
        execution.replay.has_structured_branch_history = true;
        execution.replay.next_opaque_call = then_replay
            .next_opaque_call
            .max(else_replay.next_opaque_call);
        execution.replay.next_verification_variable = then_replay
            .next_verification_variable
            .max(else_replay.next_verification_variable);
        for effect in then_arm
            .introduced_effect_facts
            .iter()
            .chain(&else_arm.introduced_effect_facts)
        {
            append_execution_effect_facts(
                &mut execution.replay.effect_facts,
                std::slice::from_ref(effect),
            );
        }
        for fact in then_arm
            .introduced_function_entry_prerequisites
            .iter()
            .chain(&else_arm.introduced_function_entry_prerequisites)
        {
            execution
                .replay
                .function_entry_execution_prerequisites
                .insert(fact.clone());
        }
        for theorem in then_arm
            .introduced_function_entry_derivations
            .iter()
            .chain(&else_arm.introduced_function_entry_derivations)
        {
            execution
                .replay
                .function_entry_derivations
                .insert(theorem.clone());
        }
        for name in then_arm
            .introduced_unfolded_predicates
            .iter()
            .chain(&else_arm.introduced_unfolded_predicates)
        {
            if !execution.replay.unfolded_predicates.contains(name) {
                execution.replay.unfolded_predicates.push(name.clone());
            }
        }
        execution.last_step_delta = ExecutionProofStepDelta::default();
        execution.branch_path.clear();
        execution.replay.case_assumptions.clear();
        let ProofContext::Execution(context) = self.root.context.as_ref() else {
            unreachable!("execution branch retained a non-execution context")
        };
        record_statement_program_point_state(
            &mut execution.replay,
            context.function_block,
            self.statement_index,
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

        let mut facts = self.root.facts().clone();
        let mut common_added_facts = Vec::new();
        for fact in &then_arm.introduced_facts {
            if else_arm.introduced_facts.contains(fact)
                && then_arm.proof.facts().contains(fact)
                && else_arm.proof.facts().contains(fact)
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
        let step = SimpleProofStep::Branch {
            ensuring: None,
            then_proof: Box::new(then_proof),
            else_proof: Box::new(else_proof),
        };
        let mut unfolded_predicates = self.root.state.unfolded_predicates.clone();
        for name in then_arm
            .introduced_unfolded_predicates
            .iter()
            .chain(&else_arm.introduced_unfolded_predicates)
        {
            unfolded_predicates.insert(name.clone());
        }
        Ok(Proof {
            context: self.root.context.clone(),
            state: Arc::new(ProofState {
                locals: self.root.state.locals.clone(),
                unfolded_predicates,
                goals: self
                    .root
                    .state
                    .goals
                    .replace_sole_frontier(facts, execution),
                added_facts: Arc::new(common_added_facts.clone()),
                checked_facts: Arc::new(common_added_facts),
            }),
            node: Arc::new(ProofNode {
                parent: Some(self.root.node.clone()),
                step: Some(Arc::new(step)),
                depth: self.root.node.depth + 1,
            }),
        })
    }
}

impl<'a> ProofScope<'a> {
    #[cfg(test)]
    pub(super) fn body(&self) -> &Proof<'a> {
        &self.body
    }

    /// The exact current kernel goal owned by this nested scope.
    pub(super) fn goal(&self) -> Option<&Proposition> {
        self.body.goal()
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

    /// Incorporates one completed scope rooted at the current body as the
    /// outer scope's next checked structural node.
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
        let body = nested.join()?;
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

    /// Opens the C branch at this scope body's current execution frontier.
    /// The branch container remains rooted at the body until its feasible
    /// arms are checked and `join_execution_branch` accepts the direct
    /// joined or decided successor.
    pub(super) fn begin_execution_branch(&self) -> Result<ExecutionProofBranches<'a>, ClickError> {
        self.body.begin_execution_branch()
    }

    /// Joins checked C arms as the next direct structural node of this scope.
    ///
    /// The exact-root checks prevent a branch searched from a sibling scope
    /// from being spliced into this one. Only facts common to the audited join
    /// are exposed as the outer scope's output-sized delta.
    pub(super) fn join_execution_branch(
        &self,
        branches: ExecutionProofBranches<'a>,
        empty: bool,
        ensuring: Option<Vec<ProofAssertion>>,
    ) -> Result<Self, ClickError> {
        if !Arc::ptr_eq(&branches.root.context, &self.body.context)
            || !Arc::ptr_eq(&branches.root.state, &self.body.state)
            || !Arc::ptr_eq(&branches.root.node, &self.body.node)
        {
            return Err(self
                .root
                .step_error("execution branches are not rooted at the current scope body"));
        }
        let body = if let Some(assertions) = ensuring {
            branches.join_with_interface(assertions)?
        } else if branches.sole_feasible_arm().is_some() {
            branches.finish_decided()?
        } else if branches.both_arms_at_function_exit() {
            branches.join_terminal()?
        } else if empty {
            branches.join_empty()?
        } else {
            branches.join()?
        };
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

    /// Applies one ordinary checked step inside the nested body. Failed
    /// candidates leave the enclosing scope value unchanged.
    #[allow(dead_code)]
    pub(super) fn apply_step(&self, step: SimpleProofStep) -> Result<Self, ClickError> {
        let mut next = self.clone();
        let body = self.body.apply_step(step)?;
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

    pub(super) fn checkpoint(&self) -> ProofCheckpoint<'a> {
        self.body.checkpoint()
    }

    pub(super) fn certificate_since(
        &self,
        checkpoint: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        self.body.certificate_since(checkpoint)
    }

    /// Checks an already-expanded, branch-shaped contextual frame through the
    /// same outcome-partition operation used by smart frame search.
    pub(super) fn apply_contextual_frame_certificate_at(
        &self,
        certificate: &ProofCertificate,
        tactic_index: usize,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        let body = self.body.apply_contextual_frame_candidate_certificate(
            certificate,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
        )?;
        let mut next = self.clone();
        next.body = body;
        Ok(next)
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
        let body = self.body.apply_step_with_origin(
            step,
            Some(ProofStepOrigin {
                tactic_index,
                source_index,
            }),
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

    /// Reports whether a terminal frame step can use the checked Proof-owned
    /// operation. Unsupported forms must leave this scope untouched so the
    /// caller can select the legacy verifier without observing a failed
    /// partial transition.
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
        let Some(body) = self.body.try_simp_closure()? else {
            return Ok(None);
        };
        let mut next = self.clone();
        next.body = body;
        Ok(Some(next))
    }

    /// Runs one supported smart script inside the owned nested body and
    /// retains its already-checked descendant.
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

    /// Checks an already-simple nested body through the same Proof API. This
    /// is used only when a surrounding smart script also owns search steps.
    fn check_certificate(&self, certificate: &ProofCertificate) -> Result<Self, ClickError> {
        let mut next = self.clone();
        next.body = self.body.check_certificate(certificate)?;
        Ok(next)
    }

    /// Applies one planner-selected candidate derivation inside this scope.
    ///
    /// The planner is untrusted and may synthesize any supported simple or
    /// structured certificate. This operation checks that candidate exactly
    /// once through the ordinary Proof transitions and retains the accepted
    /// descendant; it does not compare against separately mutated semantic
    /// aftermath or rerun an accepted candidate.
    pub(super) fn apply_candidate_certificate(
        &self,
        certificate: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        self.check_certificate(certificate)
    }

    /// Closes a completed nested proof and makes its checked proposition
    /// available in the enclosing proof while retaining the exact body.
    pub(super) fn join(self) -> Result<Proof<'a>, ClickError> {
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
                Ok(Proof {
                    context: self.root.context.clone(),
                    state: Arc::new(ProofState {
                        locals: self.root.state.locals.clone(),
                        unfolded_predicates: self.root.state.unfolded_predicates.clone(),
                        goals: self.root.state.goals.with_sole_facts(facts),
                        added_facts: Arc::new(vec![kernel.clone()]),
                        checked_facts: Arc::new(vec![kernel]),
                    }),
                    node: Arc::new(ProofNode {
                        parent: Some(self.root.node.clone()),
                        step: Some(Arc::new(SimpleProofStep::Have {
                            proposition,
                            proof: Box::new(body),
                        })),
                        depth: self.root.node.depth + 1,
                    }),
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
                state.goals = state.goals.replace_sole_frontier(facts, execution);
                state.added_facts = Arc::new(self.introduced_facts.clone());
                state.checked_facts = Arc::new(self.introduced_facts);
                Ok(Proof {
                    context: self.root.context.clone(),
                    state: Arc::new(state),
                    node: Arc::new(ProofNode {
                        parent: Some(self.root.node.clone()),
                        step: Some(Arc::new(SimpleProofStep::Open {
                            resource,
                            proof: Box::new(body),
                        })),
                        depth: self.root.node.depth + 1,
                    }),
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
        let mut normalized_exact = PersistentSet::default();
        let mut by_snapshot_blind = PersistentMap::default();
        let mut by_quantified_replay = PersistentMap::default();
        let mut implications_by_consequent = PersistentMap::default();
        let mut assumptions = PureFactContext::new();
        let mut implicit_transport_assumptions = PureFactContext::new();
        let mut direct_lowering_assumptions = PureFactContext::new();
        let mut by_predicate = PersistentMap::default();
        for fact in facts {
            if top_level_exact.contains(fact) {
                continue;
            }
            ordered.push(fact.clone());
            top_level_exact = top_level_exact.with_value(fact.clone());
            by_quantified_replay = index_quantified_replay_fact(by_quantified_replay, fact);
            implications_by_consequent =
                index_implication_consequents(implications_by_consequent, fact);
            by_predicate = index_predicate_fact(by_predicate, fact);
            if matches!(fact, Proposition::And(_, _)) {
                proper_conjuncts = index_proper_conjuncts(proper_conjuncts, fact);
                let mut conjuncts = Vec::new();
                collect_owned_atomic_conjuncts(fact, &mut conjuncts);
                for conjunct in conjuncts {
                    by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                    let normalized = normalize_direct_atomic_memory_loads(&conjunct);
                    if normalized != conjunct {
                        normalized_exact = normalized_exact.with_value(normalized);
                    }
                    exact = exact.with_value(conjunct);
                }
            } else {
                let normalized = normalize_direct_atomic_memory_loads(fact);
                if normalized != *fact {
                    normalized_exact = normalized_exact.with_value(normalized);
                }
            }
            by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, fact);
            exact = exact.with_value(fact.clone());
            assumptions = assumptions.assume_proposition(fact.clone());
            (implicit_transport_assumptions, direct_lowering_assumptions) =
                index_transport_contexts(
                    implicit_transport_assumptions,
                    direct_lowering_assumptions,
                    fact,
                );
        }
        Self {
            ordered,
            prioritized: None,
            top_level_exact,
            exact,
            proper_conjuncts,
            normalized_exact,
            by_snapshot_blind,
            by_quantified_replay,
            implications_by_consequent,
            assumptions,
            implicit_transport_assumptions,
            direct_lowering_assumptions,
            by_predicate,
        }
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
        let mut normalized_exact = self.normalized_exact.clone();
        let mut by_snapshot_blind = self.by_snapshot_blind.clone();
        let by_quantified_replay =
            index_quantified_replay_fact(self.by_quantified_replay.clone(), &fact);
        let implications_by_consequent =
            index_implication_consequents(self.implications_by_consequent.clone(), &fact);
        if matches!(fact, Proposition::And(_, _)) {
            proper_conjuncts = index_proper_conjuncts(proper_conjuncts, &fact);
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &conjunct);
                let normalized = normalize_direct_atomic_memory_loads(&conjunct);
                if normalized != conjunct {
                    normalized_exact = normalized_exact.with_value(normalized);
                }
                exact = exact.with_value(conjunct);
            }
        } else {
            let normalized = normalize_direct_atomic_memory_loads(&fact);
            if normalized != fact {
                normalized_exact = normalized_exact.with_value(normalized);
            }
        }
        by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, &fact);
        exact = exact.with_value(fact.clone());
        let mut ordered = self.ordered.clone();
        ordered.push(fact.clone());
        let (implicit_transport_assumptions, direct_lowering_assumptions) =
            index_transport_contexts(
                self.implicit_transport_assumptions.clone(),
                self.direct_lowering_assumptions.clone(),
                &fact,
            );
        Self {
            ordered,
            prioritized: self.prioritized.clone(),
            top_level_exact: self.top_level_exact.with_value(fact.clone()),
            exact,
            proper_conjuncts,
            normalized_exact,
            by_snapshot_blind,
            by_quantified_replay,
            implications_by_consequent,
            assumptions: self.assumptions.clone().assume_proposition(fact.clone()),
            implicit_transport_assumptions,
            direct_lowering_assumptions,
            by_predicate: index_predicate_fact(self.by_predicate.clone(), &fact),
        }
    }

    pub(super) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    /// Exact proper-conjunct membership with the same condition-polarity
    /// equivalence as the legacy structural checker.
    pub(super) fn contains_proper_conjunct(&self, required: &Proposition) -> bool {
        self.proper_conjuncts.contains(required)
            || condition_polarity_spellings(required)
                .iter()
                .any(|spelling| self.proper_conjuncts.contains(spelling))
    }

    /// Exact or direct-load-materialization-equivalent availability used by
    /// the deterministic rewrite rule. Unlike snapshot replay, this does not
    /// admit polarity changes or a semantic bridge beyond normalization.
    pub(super) fn materialization_available(&self, required: &Proposition) -> bool {
        if self.exact.contains(required) {
            return true;
        }
        let normalized = normalize_direct_atomic_memory_loads(required);
        self.exact.contains(&normalized) || self.normalized_exact.contains(&normalized)
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

    pub(super) fn direct_lowering_assumptions(&self) -> &PureFactContext {
        &self.direct_lowering_assumptions
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

        let normalized = normalize_direct_atomic_memory_loads(required);
        self.exact.contains(&normalized)
            || self.normalized_exact.contains(&normalized)
            || self.quantified_replay_available(required)
    }

    /// Returns one actual available fact accepted by explicit replay. Smart
    /// syntax selection needs the retained fact, not merely a yes/no answer:
    /// its recorded Surface spelling may carry a statement snapshot that the
    /// freshly lowered theorem requirement no longer exposes.
    fn matching_replay_fact_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> Option<Proposition> {
        let normalized = normalize_direct_atomic_memory_loads(required);
        let keys = [
            snapshot_blind_proposition_key(required),
            snapshot_blind_proposition_key(&normalized),
        ];
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
        // spelling even when the freshly lowered requirement is also present.
        if let Some(candidate) =
            materialization_equivalent_available_fact(required, &indexed_candidates)
        {
            return Some(candidate.clone());
        }
        if self.exact.contains(required) {
            return Some(required.clone());
        }
        if let Some(spelling) = condition_polarity_spellings(required)
            .into_iter()
            .find(|spelling| self.exact.contains(spelling))
        {
            return Some(spelling);
        }

        if self.exact.contains(&normalized) {
            return Some(normalized);
        }
        if self.normalized_exact.contains(&normalized) {
            return Some(normalized);
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
                if proposition_candidate_equals_modulo_proven_snapshots(
                    candidate,
                    required,
                    &self.assumptions,
                    framing,
                ) || snapshot_bridged_fact_is_available_under(
                    required,
                    std::slice::from_ref(candidate),
                    &self.assumptions,
                    framing,
                ) {
                    return Some(candidate.clone());
                }
            }
        }
        snapshot_bridged_fact_is_available_under(required, &candidates, &self.assumptions, framing)
            .then(|| required.clone())
    }

    fn matching_quantified_replay_fact(&self, required: &Proposition) -> Option<Proposition> {
        quantified_replay_index_key(required)
            .and_then(|key| self.by_quantified_replay.get(&key))
            .into_iter()
            .flat_map(PersistentSequence::iter)
            .find(|candidate| {
                quantified_binder_equivalent(required, candidate)
                    || quantified_replay_equivalent_available_fact(
                        required,
                        std::slice::from_ref(candidate),
                    )
                    .is_some()
            })
            .cloned()
    }

    fn quantified_replay_available(&self, required: &Proposition) -> bool {
        self.matching_quantified_replay_fact(required).is_some()
    }

    fn contains_discharged_implication_consequent(&self, required: &Proposition) -> bool {
        let normalized = normalize_direct_atomic_memory_loads(required);
        let mut keys = vec![snapshot_blind_proposition_key(required)];
        let normalized_key = snapshot_blind_proposition_key(&normalized);
        if !keys.contains(&normalized_key) {
            keys.push(normalized_key);
        }
        keys.into_iter()
            .filter_map(|key| self.implications_by_consequent.get(&key))
            .flat_map(PersistentSequence::iter)
            .any(|candidate| {
                proposition_candidate_equals_modulo_proven_snapshots(
                    &candidate.consequent,
                    required,
                    &self.assumptions,
                    &[],
                ) && candidate
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
            || condition_polarity_spellings(required)
                .iter()
                .any(|spelling| self.exact.contains(spelling))
        {
            return true;
        }

        let normalized = normalize_direct_atomic_memory_loads(required);
        let keys = [
            snapshot_blind_proposition_key(required),
            snapshot_blind_proposition_key(&normalized),
        ];
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
        snapshot_bridged_fact_is_available_under(required, &candidates, &self.assumptions, framing)
            || candidates.iter().any(|candidate| {
                proposition_candidate_equals_modulo_proven_snapshots(
                    candidate,
                    required,
                    &self.assumptions,
                    framing,
                )
            })
    }

    pub(super) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        let normalized = normalize_direct_atomic_memory_loads(fact);
        directly_conflicts_with_normalized_index(&self.exact, &normalized)
            || directly_conflicts_with_normalized_index(&self.normalized_exact, &normalized)
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
}

fn index_snapshot_fact(
    mut by_snapshot_blind: PersistentMap<
        SnapshotBlindPropositionKey,
        PersistentSequence<Proposition>,
    >,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>> {
    let normalized = normalize_direct_atomic_memory_loads(fact);
    for key in [
        snapshot_blind_proposition_key(fact),
        snapshot_blind_proposition_key(&normalized),
    ] {
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
        let normalized = normalize_direct_atomic_memory_loads(consequent);
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

fn index_transport_contexts(
    mut implicit: PureFactContext,
    mut direct_lowering: PureFactContext,
    fact: &Proposition,
) -> (PureFactContext, PureFactContext) {
    if is_implicit_fact_transport_context(fact) {
        implicit = implicit.assume_proposition(fact.clone());
    }
    let mut conjuncts = Vec::new();
    collect_owned_atomic_conjuncts(fact, &mut conjuncts);
    for conjunct in conjuncts {
        if is_direct_surface_lowering_fact(&conjunct) {
            direct_lowering = direct_lowering.assume_proposition(conjunct);
        }
    }
    (implicit, direct_lowering)
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
mod tests {
    use super::*;

    fn indexed_fact(index: u32) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(0))),
                Box::new(Bitvector32Term::Constant(index)),
            ),
            true,
        )
    }

    fn fact_node_allocations() -> usize {
        persistent_node_allocations()
    }

    fn opposite_atomic_fact(fact: &Proposition) -> Proposition {
        match fact {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => *body.clone(),
            other => Proposition::Not(Box::new(other.clone())),
        }
    }

    #[test]
    fn execution_frontier_owns_compact_selected_effect_goals() {
        let click_file = crate::lang::click::parse(
            r#"
                verifying "identity.c";
                int32 identity(int32 x) {
                    immutable;
                    ensures result == x;
                } by {
                    execute();
                    frame();
                    simp();
                }
            "#,
        )
        .expect("the effect-goal fixture should parse");
        let function_block = &click_file.function_blocks()[0];
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("the effect-goal C function should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(int32(7))];
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(&[]);
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);

        for (claim, expected, selection) in [
            (CProofClaim::Grouped, 1, EffectGoalSelection::All),
            (CProofClaim::Effect(0), 1, EffectGoalSelection::One(0)),
            (CProofClaim::Ensure(0), 0, EffectGoalSelection::None),
        ] {
            let root = Proof::for_execution_frontier(
                "typed effect goals",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: Vec::new(),
                    replay: TacticReplayState {
                        proof_site: Some(ProofSite::FunctionClaim {
                            function_name: "identity".to_string(),
                            claim,
                        }),
                        ..TacticReplayState::default()
                    },
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            assert_eq!(root.effect_goal_count(), expected);
            assert!(
                matches!(root.sole_goal(), Some(Goal::Frontier(FrontierGoal { selection: actual, .. })) if *actual == selection)
            );
            let marked = root
                .apply_step(SimpleProofStep::Mark("selected".to_string()))
                .expect("an ordinary frontier step should preserve its effect goals");
            assert_eq!(marked.effect_goal_count(), expected);
            assert!(
                matches!(marked.sole_goal(), Some(Goal::Frontier(FrontierGoal { selection: actual, .. })) if *actual == selection)
            );
        }
    }

    fn pure_identity_fixture() -> PureTheoremContext {
        PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        }
    }

    #[test]
    fn attempt_discards_failed_continuation_and_shares_the_checked_prefix() {
        let fact = indexed_fact(7);
        let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
        let theorem_context = pure_identity_fixture();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "attempt",
            &[],
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );

        // A locally successful prefix whose continuation fails is one
        // discarded candidate: the ancestor is unchanged and no partial
        // expansion is published.
        let mut budget = attempt::AttemptBudget::unbounded();
        let missed = attempt::attempt(&root, &mut budget, |candidate| {
            let prefix = attempt::candidate_outcome(candidate.apply_step(SimpleProofStep::Intro))?
                .expect("intro is locally valid on the implication goal");
            // The continuation demands a step the prefix cannot support.
            attempt::candidate_outcome(prefix.apply_step(SimpleProofStep::Split))
        })
        .expect("a rejected continuation is a miss, not a tooling failure");
        assert!(missed.is_none());
        assert!(root.certificate().steps().is_empty());
        assert!(!root.is_complete());

        // N candidate suffixes over one shared checked prefix cost N suffix
        // checks: every attempt starts from the same prefix state, which was
        // produced by exactly one accepted `Intro`.
        let prefix = root
            .apply_step(SimpleProofStep::Intro)
            .expect("intro should refine the implication goal");
        let mut attempts = 0usize;
        let mut budget = attempt::AttemptBudget::unbounded();
        let selected = attempt::first_success(
            &prefix,
            &mut budget,
            [
                SimpleProofStep::Split,
                SimpleProofStep::Left,
                SimpleProofStep::Right,
                SimpleProofStep::Assumption,
            ],
            |shared, step| {
                attempts += 1;
                assert!(Arc::ptr_eq(&shared.state, &prefix.state));
                attempt::candidate_outcome(shared.apply_step(step))
            },
        )
        .expect("candidate misses must not abort the search")
        .expect("the assumption suffix should close the goal");
        assert_eq!(attempts, 4);
        assert!(selected.is_complete());
        assert_eq!(
            selected.certificate().steps(),
            &[SimpleProofStep::Intro, SimpleProofStep::Assumption],
            "the retained certificate contains only the accepted path"
        );

        // An exhausted deterministic budget is a prompt bounded miss.
        let mut attempts = 0usize;
        let mut budget = attempt::AttemptBudget::new(1);
        let bounded = attempt::first_success(
            &prefix,
            &mut budget,
            [
                SimpleProofStep::Split,
                SimpleProofStep::Assumption,
                SimpleProofStep::Left,
            ],
            |shared, step| {
                attempts += 1;
                attempt::candidate_outcome(shared.apply_step(step))
            },
        )
        .expect("budget exhaustion is a miss, not an error");
        assert!(bounded.is_none());
        assert_eq!(attempts, 1, "only the admitted candidate may be attempted");

        // An all-or-nothing sequence discards its partial descendant.
        let mut budget = attempt::AttemptBudget::unbounded();
        let sequence = attempt::try_sequence(
            &root,
            &mut budget,
            &[SimpleProofStep::Intro, SimpleProofStep::Split],
        )
        .expect("a rejected sequence tail is a miss");
        assert!(sequence.is_none());
        let mut budget = attempt::AttemptBudget::unbounded();
        let sequence = attempt::try_sequence(
            &root,
            &mut budget,
            &[SimpleProofStep::Intro, SimpleProofStep::Assumption],
        )
        .expect("an accepted sequence is not an error")
        .expect("the checked sequence should close the goal");
        assert_eq!(
            sequence.certificate().steps(),
            &[SimpleProofStep::Intro, SimpleProofStep::Assumption]
        );
    }

    #[test]
    fn branch_split_records_children_and_rejects_a_foreign_arm() {
        let equality = |value| ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(value))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(value))),
        };
        let disjunction = ClickProposition::Or(Box::new(equality(0)), Box::new(equality(1)));
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem_context = pure_identity_fixture();
        let kernel_disjunction = lower_pure_theorem_proposition(
            "split identity",
            &disjunction,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant disjunction should lower");
        let root = Proof::for_pure_goal(
            "split identity",
            std::slice::from_ref(&kernel_disjunction),
            kernel_disjunction.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );

        // The split allocates its id and both labeled child goal ids in rule
        // order, deterministically, without touching the root's collection.
        let root_next = root.state.goals.next_id;
        let root_goal_id = root.sole_goal_id().expect("the root owns its goal");
        let branches = root
            .begin_cases(disjunction.clone())
            .expect("the exact disjunction is available");
        assert_eq!(branches.split, SplitId(root_next));
        assert_eq!(
            branches.child_goals,
            [GoalId(root_next + 1), GoalId(root_next + 2)]
        );
        assert_eq!(root.sole_goal_id(), Some(root_goal_id));
        assert_eq!(root.state.goals.next_id, root_next);
        for (arm, expected) in branches.arms.iter().zip(branches.child_goals) {
            assert_eq!(arm.sole_goal_id(), Some(expected));
        }

        // A second split of the same root is a divergent allocation: its
        // numeric ids collide, but its entry markers are distinct. An arm
        // checked under the second split must be rejected by the first
        // split's join even after both of the first split's own arms would
        // have joined successfully.
        let foreign = root
            .begin_cases(disjunction)
            .expect("the same disjunction splits again");
        assert_eq!(foreign.child_goals, branches.child_goals);
        fn close_arm<'a>(arm: &Proof<'a>) -> Proof<'a> {
            arm.try_direct_logical_closure()
                .expect("arm closure must not hit a deadline")
                .expect("each disjunct arm closes its goal directly")
        }
        let mut spliced = branches.clone();
        spliced.arms[0] = close_arm(&foreign.arms[0]);
        spliced.arms[1] = close_arm(&branches.arms[1]);
        let error = spliced
            .join()
            .err()
            .expect("a foreign arm must not satisfy this split's join");
        assert!(
            error.message().contains("did not derive from split"),
            "{error:?}"
        );
        assert!(root.certificate().steps().is_empty());

        // The legitimate arms still join, retaining only the accepted path.
        let mut branches = branches;
        branches.arms[0] = close_arm(&branches.arms[0]);
        branches.arms[1] = close_arm(&branches.arms[1]);
        let joined = branches.join().expect("both recorded arms are complete");
        assert!(joined.is_complete());
        assert!(matches!(
            joined.certificate().steps(),
            [SimpleProofStep::Cases { .. }]
        ));
    }

    #[test]
    fn attempt_reports_deadline_failure_instead_of_a_rejection() {
        let goal = indexed_fact(7);
        let theorem_context = pure_identity_fixture();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "deadline",
            &[],
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );

        // Without a deadline the unprovable candidate is an ordinary miss.
        let mut budget = attempt::AttemptBudget::unbounded();
        let missed = attempt::try_steps(&root, &mut budget, [SimpleProofStep::Assumption])
            .expect("a rejected candidate is a miss");
        assert!(missed.is_none());

        // With the deadline exceeded, the same rejection is a tooling
        // failure: the search aborts loudly instead of reading the error as
        // one more rejected candidate and continuing.
        let aborted = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            let mut budget = attempt::AttemptBudget::unbounded();
            attempt::try_steps(&root, &mut budget, [SimpleProofStep::Assumption])
        });
        assert!(
            aborted.is_err(),
            "an exceeded deadline must abort the search, not read as a miss"
        );
        let aborted = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            root.try_direct_logical_closure()
        });
        assert!(
            aborted.is_err(),
            "the shared closure search must propagate an exceeded deadline"
        );
    }

    #[test]
    fn proof_failure_preserves_ancestor_and_selected_provenance() {
        let goal = indexed_fact(7);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: vec![goal.clone()],
            surface_requirements: SurfacePropositionMap::default(),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "transactional",
            &theorem_context.requires,
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let fork = root.clone();
        assert!(Arc::ptr_eq(&root.state, &fork.state));
        assert!(Arc::ptr_eq(&root.node, &fork.node));

        assert!(
            fork.apply_step(SimpleProofStep::Normalize).is_err(),
            "a symbolic comparison must not normalize to true"
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());

        let complete = root
            .apply_step(SimpleProofStep::Assumption)
            .expect("the exact root fact should close the goal");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[SimpleProofStep::Assumption]
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn goal_identity_is_stable_across_fork_refinement_and_discharge() {
        let fact = indexed_fact(7);
        let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "identity",
            &[],
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );

        // Forking preserves every open goal's identity and allocates nothing.
        let root_id = root
            .sole_goal_id()
            .expect("a fresh proof owns its root goal");
        let fork = root.clone();
        assert_eq!(fork.sole_goal_id(), Some(root_id));

        // A goal-preserving refinement rule changes the obligation's content
        // but keeps its id and allocates no new identifier. The persistent
        // budget covers the one-node goal-map update plus inserting the
        // introduced antecedent into each fact index of this one-fact proof;
        // it must stay a small constant, not scale with proof size.
        let before_refinement = fact_node_allocations();
        let introduced = root
            .apply_step(SimpleProofStep::Intro)
            .expect("intro should refine the implication goal");
        assert_eq!(introduced.sole_goal_id(), Some(root_id));
        assert_eq!(introduced.goals_next_id(), root.goals_next_id());
        assert!(
            fact_node_allocations() - before_refinement <= 24,
            "refining the sole goal must touch only constant persistent state"
        );

        // Discharge retires the id: the collection is empty and the allocator
        // never reuses the retired identifier.
        let complete = introduced
            .apply_step(SimpleProofStep::Assumption)
            .expect("the introduced fact should close the consequent");
        assert!(complete.is_complete());
        assert_eq!(complete.sole_goal_id(), None);
        assert_eq!(complete.goals_next_id(), introduced.goals_next_id());

        // Retiring the goal in one descendant leaves the forked sibling's
        // obligation open under the same identity.
        assert_eq!(fork.sole_goal_id(), Some(root_id));
        assert!(!fork.is_complete());
        assert!(!introduced.is_complete());
    }

    #[test]
    fn certificate_suffix_requires_an_exact_shared_ancestor() {
        let fact = indexed_fact(7);
        let goal = Proposition::Implies(Box::new(fact.clone()), Box::new(fact));
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "suffix",
            &[],
            goal.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let root_checkpoint = root.checkpoint();
        let introduced = root
            .apply_step(SimpleProofStep::Intro)
            .expect("intro should create the exact antecedent fact");
        let introduced_checkpoint = introduced.checkpoint();
        let complete = introduced
            .apply_step(SimpleProofStep::Assumption)
            .expect("the introduced fact should close the consequent");

        assert_eq!(
            complete
                .certificate_since(&root_checkpoint)
                .expect("root is an ancestor")
                .steps(),
            &[SimpleProofStep::Intro, SimpleProofStep::Assumption]
        );
        assert_eq!(
            complete
                .certificate_since(&introduced_checkpoint)
                .expect("introduced proof is an ancestor")
                .steps(),
            &[SimpleProofStep::Assumption]
        );
        assert!(
            root.certificate_since(&introduced_checkpoint).is_err(),
            "a descendant cannot be used as an ancestor checkpoint"
        );

        let unrelated = Proof::for_pure_goal(
            "suffix",
            &[],
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        assert!(
            complete.certificate_since(&unrelated.checkpoint()).is_err(),
            "a structurally identical but separately rooted proof cannot be spliced"
        );
    }

    #[test]
    fn cases_branches_join_only_completed_checked_arm_proofs() {
        let equality = |value| ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(value))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(value))),
        };
        let disjunction = ClickProposition::Or(Box::new(equality(0)), Box::new(equality(1)));
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let kernel_disjunction = lower_pure_theorem_proposition(
            "cases",
            &disjunction,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant disjunction should lower");
        assert!(matches!(kernel_disjunction, Proposition::Or(_, _)));
        let root = Proof::for_pure_goal(
            "cases",
            std::slice::from_ref(&kernel_disjunction),
            kernel_disjunction.clone(),
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let branches = root
            .begin_cases(disjunction.clone())
            .expect("the exact disjunction should open two cases");
        assert!(branches.clone().join().is_err());
        assert!(
            branches
                .apply_step(ProofArm::Left, SimpleProofStep::Intro)
                .is_err(),
            "a rejected arm candidate must not mutate the branch set"
        );
        assert!(
            branches
                .arm(ProofArm::Left)
                .certificate()
                .steps()
                .is_empty()
        );

        let branches = branches
            .apply_step(ProofArm::Left, SimpleProofStep::Left)
            .expect("left disjunct should close the left arm");
        assert!(branches.arm(ProofArm::Left).is_complete());
        assert!(!branches.arm(ProofArm::Right).is_complete());
        let branches = branches
            .apply_step(ProofArm::Right, SimpleProofStep::Right)
            .expect("right disjunct should close the right arm");
        let joined = branches.join().expect("both checked arms should join");
        assert!(joined.is_complete());
        assert_eq!(
            joined.certificate().steps(),
            &[SimpleProofStep::Cases {
                disjunction,
                left_proof: Box::new(ProofCertificate::from_steps(vec![SimpleProofStep::Left,])),
                right_proof: Box::new(ProofCertificate::from_steps(vec![SimpleProofStep::Right,])),
            }]
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn have_scope_publishes_only_a_completed_checked_body() {
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let kernel = lower_pure_theorem_proposition(
            "have",
            &proposition,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");
        let root = Proof::for_pure_goal(
            "have",
            &[],
            kernel,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let scope = root
            .begin_have(proposition.clone())
            .expect("have should open a nested proposition proof");
        assert!(scope.clone().join().is_err());
        assert!(scope.apply_step(SimpleProofStep::Intro).is_err());
        assert!(scope.body().certificate().steps().is_empty());

        let scope = scope
            .apply_step(SimpleProofStep::Normalize)
            .expect("constant equality should normalize inside the body");
        let enclosing = scope.join().expect("completed body should close the scope");
        assert!(!enclosing.is_complete());
        assert_eq!(enclosing.added_facts().len(), 1);
        let complete = enclosing
            .apply_step(SimpleProofStep::Assumption)
            .expect("published have fact should close the enclosing goal");
        assert_eq!(
            complete.certificate().steps(),
            &[
                SimpleProofStep::Have {
                    proposition,
                    proof: Box::new(ProofCertificate::from_steps(vec![
                        SimpleProofStep::Normalize,
                    ])),
                },
                SimpleProofStep::Assumption,
            ]
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn smart_have_scope_scales_with_local_output_and_is_transactional() {
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let memory = CMemory::new();
        let kernel = lower_pure_theorem_proposition(
            "smart have scaling",
            &proposition,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");
        let smart_body = [ProofTactic::Simp];
        let missing_body = [
            ProofTactic::ApplyTheorem(TheoremApplication {
                name: "missing".to_string(),
                arguments: Vec::new(),
            }),
            ProofTactic::Simp,
        ];

        for size in [16_u32, 64, 256, 1024, 4096] {
            let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let theorem_context = PureTheoremContext {
                memory: memory.clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: requires.clone(),
                surface_requirements: SurfacePropositionMap::default(),
            };
            let root = Proof::for_pure_goal(
                "smart have scaling",
                &requires,
                kernel.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let scope = root
                .begin_have(proposition.clone())
                .expect("have should open a nested proof");
            assert!(
                scope
                    .try_linear_smart_script(&missing_body)
                    .expect("an unknown theorem should be a bounded smart-search miss")
                    .is_none(),
                "an unknown theorem must not manufacture a nested descendant"
            );
            assert!(scope.body().certificate().steps().is_empty());

            let before = fact_node_allocations();
            let selected = scope
                .try_linear_smart_script(&smart_body)
                .expect("nested smart search should not fail")
                .expect("simp should close the constant equality");
            let enclosing = selected
                .join()
                .expect("the completed nested proof should join");
            let complete = enclosing
                .apply_step(SimpleProofStep::Assumption)
                .expect("the published have fact should close the outer goal");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 64 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} smart scope allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                complete.certificate().steps(),
                &[
                    SimpleProofStep::Have {
                        proposition: proposition.clone(),
                        proof: Box::new(ProofCertificate::from_steps(vec![
                            SimpleProofStep::Normalize,
                        ])),
                    },
                    SimpleProofStep::Assumption,
                ]
            );
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn persistent_fact_lookup_scales_logarithmically() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        for size in [16_u32, 64, 256, 1024, 4096] {
            let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let goal = indexed_fact(size - 1);
            let theorem_context = PureTheoremContext {
                memory: CMemory::new(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires,
                surface_requirements: SurfacePropositionMap::default(),
            };
            let proof = Proof::for_pure_goal(
                "scaling",
                &theorem_context.requires,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let shared = proof.clone();
            assert!(Arc::ptr_eq(&proof.state, &shared.state));
            assert!(Arc::ptr_eq(&proof.node, &shared.node));

            let comparisons = proof.fact_lookup_comparisons(&goal);
            let logarithmic_bound = 2 * (u32::BITS - size.leading_zeros()) as usize + 2;
            assert!(
                comparisons <= logarithmic_bound,
                "size {size} lookup took {comparisons} comparisons (bound {logarithmic_bound})"
            );

            let complete = shared
                .apply_step(SimpleProofStep::Assumption)
                .expect("fixed local step should succeed");
            assert!(complete.is_complete());
            assert!(Arc::ptr_eq(
                complete
                    .node
                    .parent
                    .as_ref()
                    .expect("successor has a parent"),
                &proof.node
            ));
            assert!(proof.certificate().steps().is_empty());
            assert_eq!(complete.certificate().steps().len(), 1);
        }
    }

    #[test]
    fn proof_fact_forks_share_context_and_local_insertions_are_logarithmic() {
        let mut allocation_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let facts = ProofFacts::from_ordered(&initial);
            let fork = facts.clone();
            assert!(facts.exact.shares_root_with(&fork.exact));
            assert!(
                facts
                    .assumptions
                    .shares_persistent_storage_with(&fork.assumptions)
            );

            let added = indexed_fact(size + 1);
            let before = fact_node_allocations();
            let successor = fork.with_fact(added.clone());
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            allocation_samples.push((size, logarithmic_height, allocations));
            assert!(!facts.contains(&added));
            assert!(successor.contains(&added));
            assert!(successor.assumptions.proves(&added));
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        assert!(
            base_allocations <= 48,
            "small persistent fact insertion allocated {base_allocations} nodes"
        );
        for (size, height, allocations) in allocation_samples {
            // A condition fact updates the exact and normalized indexes, the
            // kernel condition map, and the two endpoint maps in its signed
            // order index. Every one is an AVL path copy; adding two tree
            // levels may therefore add at most 24 nodes.
            let allocation_bound = base_allocations + 12 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} local insertion allocated {allocations} fact nodes (logarithmic bound {allocation_bound})"
            );
        }
    }

    #[test]
    fn statement_fact_prefix_preserves_successor_order_without_copying_ambient_history() {
        let first = indexed_fact(1);
        let promoted = indexed_fact(2);
        let added = indexed_fact(3);
        let facts = ProofFacts::from_ordered(&[first.clone(), promoted.clone()]);
        let ambient_tail = facts.ordered.clone();
        let successor = facts.with_statement_facts(vec![promoted.clone(), added.clone()]);

        assert!(successor.ordered.shares_tail_with(&ambient_tail));
        assert_eq!(successor.to_vec(), vec![promoted, added, first]);
    }

    #[test]
    fn replay_availability_probes_equivalent_condition_polarities_by_exact_index() {
        let left = Bitvector32Term::Variable(Variable(80_000));
        let right = Bitvector32Term::Variable(Variable(80_001));
        let available = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ),
            true,
        );
        let facts = ProofFacts::from_ordered(&[available]);
        for required in [
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(left.clone()),
                    Box::new(right.clone()),
                ),
                false,
            ),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(right.clone()),
                    Box::new(left.clone()),
                ),
                false,
            ),
            Proposition::Not(Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterThan(
                    Box::new(right.clone()),
                    Box::new(left.clone()),
                ),
                false,
            ))),
        ] {
            assert!(facts.replay_available_across_effects(&required, &[]));
        }
    }

    #[test]
    fn proof_fact_predicate_index_ignores_unrelated_context() {
        let name = "selected".to_string();
        let predicate = Proposition::Predicate {
            name: name.clone(),
            arguments: Vec::new(),
        };
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut initial = (0..size).map(indexed_fact).collect::<Vec<_>>();
            initial.push(predicate.clone());
            let facts = ProofFacts::from_ordered(&initial);
            let fork = facts.clone();

            assert!(facts.ordered.shares_tail_with(&fork.ordered));
            assert!(facts.exact.shares_root_with(&fork.exact));
            assert!(facts.by_predicate.shares_root_with(&fork.by_predicate));
            assert_eq!(facts.to_vec(), initial);
            assert_eq!(
                facts.mentioning_predicate(&name).collect::<Vec<_>>(),
                vec![&predicate]
            );
        }
    }

    #[test]
    fn proposition_unfold_uses_indexed_facts_and_persistent_local_state() {
        let click_file = crate::lang::click::parse(
            r#"
                predicate selected(x: int32) { x == x }
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test predicate should parse");
        let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let predicate_surface = ClickProposition::PredicateCall {
            name: "selected".to_string(),
            arguments: vec![ContractExpression::CFragment(CExpression::Value(int32(7)))],
        };
        let goal_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(7))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let base_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let lower = |surface: &ClickProposition| {
            lower_pure_theorem_proposition(
                "persistent proposition unfold",
                surface,
                &base_context.values,
                &base_context.array_refs,
                &base_context.memory,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("test proposition should lower")
        };
        let predicate = lower(&predicate_surface);
        let goal = lower(&goal_surface);

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.push(predicate.clone());
            let theorem_context = PureTheoremContext {
                requires: requires.clone(),
                ..base_context.clone()
            };
            let root = Proof::for_pure_surface_goal(
                "persistent proposition unfold",
                &requires,
                predicate.clone(),
                predicate_surface.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            assert_eq!(
                root.facts()
                    .mentioning_predicate(&"selected".to_string())
                    .collect::<Vec<_>>(),
                vec![&predicate],
                "unrelated facts must not enter the selected predicate bucket"
            );
            assert!(
                root.apply_step(SimpleProofStep::UnfoldPredicate("missing".to_string()))
                    .is_err(),
                "an unknown predicate must reject transactionally"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let unfold = SimpleProofStep::UnfoldPredicate("selected".to_string());
            let before = fact_node_allocations();
            let unfolded = root
                .apply_step(unfold.clone())
                .expect("the selected predicate fact and goal should unfold");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 40 * logarithmic_height + 160;
            assert!(
                allocations <= allocation_bound,
                "size {size} proposition unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(unfolded.facts().contains(&goal));
            assert_eq!(unfolded.goal(), Some(&goal));
            assert_eq!(unfolded.surface_goal(), Some(&goal_surface));
            assert!(
                unfolded
                    .state
                    .unfolded_predicates
                    .contains(&"selected".to_string())
            );
            let complete = unfolded
                .apply_step(SimpleProofStep::Assumption)
                .expect("the unfolded predicate fact should close the unfolded goal");
            assert!(complete.is_complete());
            assert_eq!(
                complete.certificate().steps(),
                &[unfold.clone(), SimpleProofStep::Assumption]
            );

            let certificate =
                ProofCertificate::from_steps(vec![unfold.clone(), SimpleProofStep::Assumption]);
            let checked = root
                .check_certificate(&certificate)
                .expect("an explicit proposition unfold certificate should check through Proof");
            assert!(checked.is_complete());
            assert_eq!(checked.certificate(), certificate);
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_proposition_unfold_checks_the_same_retained_step() {
        let click_file = crate::lang::click::parse(
            r#"
                predicate selected(x: int32) { x == x }
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test predicate should parse");
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test function should parse");
        let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let state = CState::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let program_point_states = ProgramPointStates::new();
        let predicate_surface = ClickProposition::PredicateCall {
            name: "selected".to_string(),
            arguments: vec![ContractExpression::CFragment(CExpression::Value(int32(7)))],
        };
        let goal_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(7))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("point proposition should lower")
        };
        let predicate = lower(&predicate_surface);
        let goal = lower(&goal_surface);
        let surface_propositions = SurfacePropositionMap::default();
        let root = Proof::for_point_goal(
            "point proposition unfold",
            0,
            std::slice::from_ref(&predicate),
            goal.clone(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let certificate = ProofCertificate::from_steps(vec![
            SimpleProofStep::UnfoldPredicate("selected".to_string()),
            SimpleProofStep::Assumption,
        ]);
        let checked = root
            .check_certificate(&certificate)
            .expect("point unfold should use the shared predicate transition");
        assert!(checked.is_complete());
        assert_eq!(checked.certificate(), certificate);
        assert!(root.certificate().steps().is_empty());

        let result = int32(7);
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(predicate.clone());
            let root = Proof::for_point_frontier(
                "result-aware point-frontier unfold",
                0,
                &facts,
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                Some(&result),
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            assert!(
                root.apply_step(SimpleProofStep::UnfoldPredicate("missing".to_string()))
                    .is_err()
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));

            let step = SimpleProofStep::UnfoldPredicate("selected".to_string());
            let before = fact_node_allocations();
            let unfolded = root
                .apply_step(step.clone())
                .expect("a point frontier should accept a facts-only predicate unfold");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 40 * logarithmic_height + 160;
            assert!(
                allocations <= allocation_bound,
                "size {size} result-aware frontier unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(unfolded.certificate().steps(), &[step]);
            assert_eq!(unfolded.added_facts(), std::slice::from_ref(&goal));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_proof_root_borrows_inherited_unfold_history_without_reindexing_it() {
        let inherited = (0..4096)
            .map(|index| format!("predicate_{index}"))
            .collect::<Vec<_>>();
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let goal = indexed_fact(7);
        let before = fact_node_allocations();
        let root = Proof::for_point_goal(
            "borrowed unfold history",
            0,
            &[],
            goal,
            &[],
            &[],
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &inherited,
            &[],
        );
        let allocations = fact_node_allocations() - before;
        // The one permitted node stores the root goal in the persistent goal
        // collection; the bound must stay independent of the inherited size.
        assert!(
            allocations <= 1,
            "creating a point Proof must not rebuild inherited unfold history \
             ({allocations} persistent nodes allocated)"
        );
        assert_eq!(root.state.unfolded_predicates.len(), 0);
        assert_eq!(root.active_unfolded_predicates(), inherited);
    }

    #[test]
    fn result_aware_point_goal_focus_shares_facts_and_checks_assumption() {
        let state = CState::new();
        let result = int32(0);
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let goal = indexed_fact(9_000_000);
        let missing = indexed_fact(9_000_001);

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(goal.clone());
            let root = Proof::for_point_frontier(
                "result-aware point goal focus",
                0,
                &facts,
                &[],
                &[],
                &state,
                &state,
                Some(&result),
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let before = fact_node_allocations();
            let focused = root
                .focus_point_goal(goal.clone())
                .expect("an initial point frontier should focus one ensure goal");
            // The one permitted node stores the focused root goal in the
            // fresh proof's goal collection; every fact index stays shared.
            assert!(
                fact_node_allocations() - before <= 1,
                "focusing a goal must share every persistent fact index"
            );
            assert!(root.facts().exact.shares_root_with(&focused.facts().exact));
            let retained_focused = focused.clone();
            assert!(
                root.focus_point_goal(missing.clone())
                    .expect("focusing does not prove the selected goal")
                    .apply_step(SimpleProofStep::Assumption)
                    .is_err()
            );
            assert!(Arc::ptr_eq(&focused.state, &retained_focused.state));

            let complete = focused
                .apply_step(SimpleProofStep::Assumption)
                .expect("the focused exact goal should close through Proof");
            assert!(complete.is_complete());
            assert_eq!(
                complete.certificate().steps(),
                &[SimpleProofStep::Assumption]
            );
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_frontier_have_publishes_checked_fact_for_later_scope() {
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test function should parse");
        let state = CState::new();
        let result = int32(0);
        let arguments = vec![CExpression::Value(result.clone())];
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let proposition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let root = Proof::for_point_frontier(
                "point frontier have",
                0,
                &facts,
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                Some(&result),
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let first = root
                .begin_have(proposition.clone())
                .expect("a point frontier should open a checked have scope")
                .apply_step(SimpleProofStep::Normalize)
                .expect("the first scope should prove the concrete equality")
                .join()
                .expect("a completed point-frontier scope should publish its fact");
            let second = first
                .begin_have(proposition.clone())
                .expect("the checked successor should open a dependent scope")
                .apply_step(SimpleProofStep::Assumption)
                .expect("the later scope should see the first checked fact")
                .join()
                .expect("the dependent scope should publish its retained proof");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 40 * logarithmic_height + 160;
            assert!(
                allocations <= allocation_bound,
                "size {size} two-scope point proof allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(matches!(
                second.certificate().steps(),
                [
                    SimpleProofStep::Have { proof: first, .. },
                    SimpleProofStep::Have { proof: second, .. }
                ] if first.steps() == [SimpleProofStep::Normalize]
                    && second.steps() == [SimpleProofStep::Assumption]
            ));
            let completed = second
                .complete_point_obligations(std::slice::from_ref(&proposition))
                .expect("the accumulated frontier should close its external obligation");
            assert!(matches!(
                completed.steps(),
                [
                    SimpleProofStep::Have { .. },
                    SimpleProofStep::Have { .. },
                    SimpleProofStep::Assumption
                ]
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_frontier_have_goal_does_not_reuse_an_older_surface_lowering() {
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test function should parse");
        let state = CState::new();
        let result = int32(1);
        let arguments = vec![CExpression::Value(result.clone())];
        let program_point_states = ProgramPointStates::new();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let older = indexed_fact(9_200_000);
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&surface, &older)
            .expect("the older spelling should be recorded");
        let root = Proof::for_point_frontier(
            "point have current goal",
            0,
            std::slice::from_ref(&older),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let scope = root
            .begin_have(surface)
            .expect("the current point goal should lower independently");
        assert!(
            scope.apply_step(SimpleProofStep::Assumption).is_err(),
            "an older fact with the same surface spelling must not close the current goal"
        );
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn proof_if_fork_and_join_work_is_logarithmic_in_unrelated_facts() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let condition = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let surface_goal = ClickProposition::Or(
            Box::new(condition.clone()),
            Box::new(ClickProposition::Not(Box::new(condition.clone()))),
        );

        for size in [16_u32, 64, 256, 1024, 4096] {
            let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let theorem_context = PureTheoremContext {
                memory: CMemory::new(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires,
                surface_requirements: SurfacePropositionMap::default(),
            };
            let goal = lower_pure_theorem_proposition(
                "branch scaling",
                &surface_goal,
                &theorem_context.values,
                &theorem_context.array_refs,
                &theorem_context.memory,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("excluded-middle goal should lower");
            let root = Proof::for_pure_goal(
                "branch scaling",
                &theorem_context.requires,
                goal,
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let before = fact_node_allocations();
            let branches = root
                .begin_if(condition.clone())
                .expect("proof if should create two checked arms");
            let branch_allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 8 * logarithmic_height + 16;
            assert!(
                branch_allocations <= allocation_bound,
                "size {size} branch fork allocated {branch_allocations} fact nodes (bound {allocation_bound})"
            );

            let joined = branches
                .apply_step(ProofArm::Left, SimpleProofStep::Left)
                .expect("the condition closes the then arm")
                .apply_step(ProofArm::Right, SimpleProofStep::Right)
                .expect("the exact negation closes the else arm")
                .join()
                .expect("both checked descendants should join");
            assert!(joined.is_complete());
            assert_eq!(joined.certificate().steps().len(), 1);
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::If { then_proof, else_proof, .. }]
                    if then_proof.steps() == [SimpleProofStep::Left]
                        && else_proof.steps() == [SimpleProofStep::Right]
            ));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn execution_frontier_rejects_proposition_closers_transactionally() {
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_point_frontier(
            "frontier",
            0,
            &[],
            &[],
            &[],
            &state,
            &state,
            None,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        let fork = root.clone();
        assert!(root.goal().is_none());
        assert!(Arc::ptr_eq(&root.state, &fork.state));
        assert!(Arc::ptr_eq(&root.node, &fork.node));
        for closer in [SimpleProofStep::Assumption, SimpleProofStep::Normalize] {
            let error = fork
                .apply_step(closer)
                .err()
                .expect("a proposition closer cannot close an execution frontier");
            assert!(error.message().contains("proposition goal"), "{error:?}");
        }
        assert!(!root.is_complete());
        assert!(root.added_facts().is_empty());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn point_witness_refines_existential_transactionally_with_constant_local_work() {
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let variable = Variable(9_000_000);
        let expected = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::Constant(7)),
            ),
            true,
        );
        let goal = Proposition::Exists {
            name: "chosen".to_string(),
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(expected),
        };
        let witness = ProofWitness {
            name: "chosen".to_string(),
            value: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let expected_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("chosen".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let surface_goal = ClickProposition::Exists {
            c_type: C0Type::Int32,
            name: "chosen".to_string(),
            body: Box::new(expected_surface),
        };
        let instantiated_surface = ClickProposition::Comparison {
            left: witness.value.clone(),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let root = Proof::for_point_surface_goal(
                "persistent witness",
                0,
                &facts,
                goal.clone(),
                surface_goal.clone(),
                &[],
                &[],
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let wrong_name = SimpleProofStep::Witness(ProofWitness {
                name: "other".to_string(),
                value: ContractExpression::CFragment(CExpression::Value(int32(7))),
            });
            let error = root
                .apply_step(wrong_name)
                .err()
                .expect("a mismatched witness must reject the candidate");
            assert!(error.message().contains("binds `chosen`"), "{error:?}");
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let before = fact_node_allocations();
            let refined = root
                .apply_step(SimpleProofStep::Witness(witness.clone()))
                .expect("the named int32 witness should refine the existential");
            let allocations = fact_node_allocations() - before;
            // The one permitted node rewrites the sole entry of the goal
            // collection; the bound must stay independent of `size` because
            // the witness never touches the persistent fact index.
            assert!(
                allocations <= 1,
                "size {size} witness should not alter the persistent fact index \
                 ({allocations} persistent nodes allocated)"
            );
            assert_eq!(
                refined.certificate().steps(),
                &[SimpleProofStep::Witness(witness.clone())]
            );
            assert_eq!(refined.surface_goal(), Some(&instantiated_surface));
            assert!(refined.added_facts().is_empty());
            assert!(!refined.is_complete());
            let completed = refined
                .apply_step(SimpleProofStep::Normalize)
                .expect("the instantiated constant equality should normalize");
            assert!(completed.is_complete());
            assert_eq!(
                completed.certificate().steps(),
                &[
                    SimpleProofStep::Witness(witness.clone()),
                    SimpleProofStep::Normalize,
                ]
            );
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_choose_uses_indexed_requirement_and_persistent_local_bindings() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 choose_source(int32 x) {
                    requires source: exists (k: int32) { k == x };
                    ensures result == x by { assumption(); }
                }
            "#,
        )
        .expect("labeled existential requirement should parse");
        let function_block = &click_file.function_blocks()[0];
        assert_eq!(
            function_block.requirement_label_indices().get("source"),
            Some(&0),
            "the parser should build the requirement-label index once"
        );
        let parsed_function = syntax::parse_function("int32 choose_source(int32 x) { return x; }")
            .expect("test function should parse");
        let state = CState::new().with_local("x", int32(7));
        let arguments = vec![CExpression::Value(int32(7))];
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let source_variable = Variable(9_200_000);
        let source_fact = Proposition::Exists {
            name: "source_value".to_string(),
            var: source_variable,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(source_variable)),
                    Box::new(Bitvector32Term::Constant(7)),
                ),
                true,
            )),
        };
        let goal_variable = Variable(9_200_001);
        let goal = Proposition::Exists {
            name: "witness".to_string(),
            var: goal_variable,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(goal_variable)),
                    Box::new(Bitvector32Term::Constant(7)),
                ),
                true,
            )),
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = vec![source_fact.clone()];
            facts.extend((0..size).map(indexed_fact));
            let root = Proof::for_point_goal_with_requirements(
                "persistent choose",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                None,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
                function_block.requires(),
                function_block.requirement_label_indices(),
            );
            let retained_root = root.clone();
            let missing = root
                .apply_step(SimpleProofStep::Choose(ProofChoice {
                    name: "candidate".to_string(),
                    source: ProofFactSource::RequirementLabel("missing".to_string()),
                }))
                .err()
                .expect("an unknown label must reject the candidate");
            assert!(missing.message().contains("unknown requirement label"));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));

            let choice = ProofChoice {
                name: "candidate".to_string(),
                source: ProofFactSource::RequirementLabel("source".to_string()),
            };
            let before = fact_node_allocations();
            let chosen = root
                .apply_step(SimpleProofStep::Choose(choice.clone()))
                .expect("the indexed existential requirement should introduce one local");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 48 * logarithmic_height + 64;
            assert!(
                allocations <= allocation_bound,
                "size {size} choose allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                chosen.certificate().steps(),
                &[SimpleProofStep::Choose(choice.clone())]
            );
            assert_eq!(chosen.state.locals.values.len(), 1);
            assert!(root.state.locals.values.is_empty());

            let duplicate = chosen
                .apply_step(SimpleProofStep::Choose(choice.clone()))
                .err()
                .expect("a duplicate local name must reject transactionally");
            assert!(duplicate.message().contains("already in scope"));
            assert_eq!(
                chosen.certificate().steps(),
                &[SimpleProofStep::Choose(choice)]
            );

            let completed = chosen
                .apply_step(SimpleProofStep::Witness(ProofWitness {
                    name: "witness".to_string(),
                    value: ContractExpression::CFragment(CExpression::Variable(
                        "candidate".to_string(),
                    )),
                }))
                .expect("witness should resolve the one referenced proof local")
                .apply_step(SimpleProofStep::Assumption)
                .expect("the chosen existential fact should close the refined goal");
            assert!(completed.is_complete());
            assert!(matches!(
                completed.certificate().steps(),
                [
                    SimpleProofStep::Choose(_),
                    SimpleProofStep::Witness(_),
                    SimpleProofStep::Assumption
                ]
            ));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn pure_rewrite_uses_indexed_equality_availability_without_changing_facts() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let equality = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable("y".to_string())),
        };
        let unavailable = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("z".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable("w".to_string())),
        };
        let values = BTreeMap::from([
            (
                "x".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_100_000))),
            ),
            ("y".to_string(), int32(1)),
            (
                "z".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_100_001))),
            ),
            ("w".to_string(), int32(3)),
        ]);
        let base_context = PureTheoremContext {
            memory: CMemory::new(),
            values,
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let kernel_equality = lower_pure_theorem_proposition(
            "persistent rewrite",
            &equality,
            &base_context.values,
            &base_context.array_refs,
            &base_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.push(kernel_equality.clone());
            let theorem_context = PureTheoremContext {
                requires: requires.clone(),
                ..base_context.clone()
            };
            let root = Proof::for_pure_surface_goal(
                "persistent rewrite",
                &requires,
                kernel_equality.clone(),
                equality.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let error = root
                .apply_step(SimpleProofStep::Rewrite(unavailable.clone()))
                .err()
                .expect("an unavailable equality must reject the candidate");
            assert!(
                error.message().contains("exact available fact"),
                "{error:?}"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let step = SimpleProofStep::Rewrite(equality.clone());
            let before = fact_node_allocations();
            let rewritten = root
                .apply_step(step.clone())
                .expect("the exact available equality should rewrite the goal");
            let allocations = fact_node_allocations() - before;
            // The one permitted node rewrites the sole entry of the goal
            // collection; the bound must stay independent of `size` because
            // the rewrite never touches the persistent fact index.
            assert!(
                allocations <= 1,
                "size {size} rewrite should not alter the persistent fact index \
                 ({allocations} persistent nodes allocated)"
            );
            assert_eq!(rewritten.certificate().steps(), &[step.clone()]);
            assert!(
                rewritten.surface_goal().is_none(),
                "a Surface spelling that lowers through extra normalization must not be paired with the unnormalized kernel successor"
            );
            assert!(rewritten.added_facts().is_empty());
            assert!(!rewritten.is_complete());
            let complete = rewritten
                .apply_step(SimpleProofStep::Normalize)
                .expect("the rewritten constant equality should normalize");
            assert!(complete.is_complete());
            assert_eq!(
                complete.certificate().steps(),
                &[step.clone(), SimpleProofStep::Normalize]
            );
            let alternative = root
                .apply_step(step)
                .expect("the ancestor should remain usable for another descendant");
            assert_eq!(alternative.certificate(), rewritten.certificate());
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn surface_rewrite_retains_structural_successor_and_scales() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let variable =
            |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
        let zero = ContractExpression::CFragment(CExpression::Value(int32(0)));
        let comparison =
            |left: ContractExpression, operator: ComparisonOperator, right: ContractExpression| {
                ClickProposition::Comparison {
                    left,
                    operator,
                    right,
                }
            };
        let equality = comparison(variable("x"), ComparisonOperator::Equal, variable("y"));
        let y_zero = comparison(variable("y"), ComparisonOperator::Equal, zero.clone());
        let z_zero = comparison(variable("z"), ComparisonOperator::Equal, zero.clone());
        let goal_surface = ClickProposition::And(
            Box::new(comparison(
                variable("x"),
                ComparisonOperator::LessEqual,
                zero.clone(),
            )),
            Box::new(comparison(
                variable("z"),
                ComparisonOperator::LessEqual,
                zero.clone(),
            )),
        );
        let rewritten_surface = ClickProposition::And(
            Box::new(comparison(
                variable("y"),
                ComparisonOperator::LessEqual,
                zero.clone(),
            )),
            Box::new(comparison(
                variable("z"),
                ComparisonOperator::LessEqual,
                zero,
            )),
        );
        let values = BTreeMap::from([
            (
                "x".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_101_000))),
            ),
            (
                "y".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_101_001))),
            ),
            (
                "z".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(9_101_002))),
            ),
        ]);
        let base_context = PureTheoremContext {
            memory: CMemory::new(),
            values,
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let lower = |surface: &ClickProposition| {
            lower_pure_theorem_proposition(
                "persistent structural rewrite",
                surface,
                &base_context.values,
                &base_context.array_refs,
                &base_context.memory,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("test proposition should lower")
        };
        let kernel_equality = lower(&equality);
        let kernel_y_zero = lower(&y_zero);
        let kernel_z_zero = lower(&z_zero);
        let kernel_goal = lower(&goal_surface);
        let rewritten_kernel_goal = lower(&rewritten_surface);
        let mut surface_requirements = SurfacePropositionMap::default();
        for (surface, kernel) in [
            (&equality, &kernel_equality),
            (&y_zero, &kernel_y_zero),
            (&z_zero, &kernel_z_zero),
        ] {
            surface_requirements
                .record_lowering(surface, kernel)
                .expect("selected rewrite premise should have an exact spelling");
        }

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.extend([
                kernel_equality.clone(),
                kernel_y_zero.clone(),
                kernel_z_zero.clone(),
            ]);
            let theorem_context = PureTheoremContext {
                requires: requires.clone(),
                surface_requirements: surface_requirements.clone(),
                ..base_context.clone()
            };
            let root = Proof::for_pure_surface_goal(
                "persistent structural rewrite",
                &requires,
                kernel_goal.clone(),
                goal_surface.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let rewritten = root
                .apply_step(SimpleProofStep::Rewrite(equality.clone()))
                .expect("the exact equality should produce a checked rewrite successor");
            let closed = rewritten
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the rewritten Surface conjunction should retain both child proofs");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} structural rewrite allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(rewritten.goal(), Some(&rewritten_kernel_goal));
            assert_eq!(rewritten.surface_goal(), Some(&rewritten_surface));
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [
                    SimpleProofStep::Rewrite(root_equality),
                    SimpleProofStep::Have { proof: left, .. },
                    SimpleProofStep::Have { proof: right, .. },
                    SimpleProofStep::Split,
                ] if root_equality == &equality
                    && matches!(left.steps(), [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize])
                    && matches!(right.steps(), [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize])
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_extract_uses_persistent_proper_conjunct_membership() {
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(7))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let kernel = lower_point_proposition_with_assumptions(
            &surface,
            &PureFactContext::new(),
            &[],
            &[],
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower");

        let merely_top_level = Proof::for_point_goal(
            "top-level is not a proper conjunct",
            0,
            std::slice::from_ref(&kernel),
            kernel.clone(),
            &[],
            &[],
            &state,
            &state,
            &program_point_states,
            &surface_propositions,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
            &[],
            &[],
        );
        assert!(
            merely_top_level
                .apply_step(SimpleProofStep::Extract(surface.clone()))
                .is_err(),
            "an independently available fact is not extractable unless it is also a proper conjunct"
        );

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
            available.push(Proposition::And(
                Box::new(indexed_fact(size + 1)),
                Box::new(Proposition::And(
                    Box::new(kernel.clone()),
                    Box::new(indexed_fact(size + 2)),
                )),
            ));
            let root = Proof::for_point_goal(
                "persistent extract",
                0,
                &available,
                kernel.clone(),
                &[],
                &[],
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let step = SimpleProofStep::Extract(surface.clone());
            let before = fact_node_allocations();
            let extracted = root
                .apply_step(step.clone())
                .expect("the nested proper conjunct should extract");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 32 * logarithmic_height + 128;
            assert!(
                allocations <= allocation_bound,
                "size {size} extract allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert_eq!(extracted.certificate().steps(), &[step]);
            assert_eq!(extracted.added_facts(), std::slice::from_ref(&kernel));
            assert!(extracted.is_complete());
        }
    }

    #[test]
    fn implication_extract_uses_indexed_consequent_and_alpha_equivalent_antecedent() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let target_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::from([(
                "x".to_string(),
                CValue::Int32(Bitvector32Term::Variable(Variable(8_000_000))),
            )]),
            array_refs: BTreeMap::new(),
            requires: Vec::new(),
            surface_requirements: SurfacePropositionMap::default(),
        };
        let target = lower_pure_theorem_proposition(
            "indexed implication extract",
            &target_surface,
            &theorem_context.values,
            &theorem_context.array_refs,
            &theorem_context.memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("target should lower");
        let universal = |variable| Proposition::ForAll {
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Variable(variable)),
                ),
                true,
            )),
        };
        let required_antecedent = universal(Variable(8_100_000));
        let available_antecedent = universal(Variable(8_200_000));
        let selected_implication = Proposition::Implies(
            Box::new(required_antecedent.clone()),
            Box::new(target.clone()),
        );

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size)
                .map(|index| {
                    Proposition::Implies(
                        Box::new(indexed_fact(100_000 + index)),
                        Box::new(indexed_fact(200_000 + index)),
                    )
                })
                .collect::<Vec<_>>();
            facts.push(available_antecedent.clone());
            facts.push(selected_implication.clone());
            let root = Proof::for_pure_goal(
                "indexed implication extract",
                &facts,
                target.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let target_key = snapshot_blind_proposition_key(&target);
            assert_eq!(
                root.facts()
                    .implications_by_consequent
                    .get(&target_key)
                    .expect("selected consequent should be indexed")
                    .len(),
                1,
                "unrelated implications must not enter the selected bucket"
            );
            let quantified_key = quantified_replay_index_key(&required_antecedent)
                .expect("a universal has an alpha-invariant key");
            assert_eq!(
                root.facts()
                    .by_quantified_replay
                    .get(&quantified_key)
                    .expect("alpha-equivalent antecedent should be indexed")
                    .len(),
                1
            );

            let step = SimpleProofStep::Extract(target_surface.clone());
            let before = fact_node_allocations();
            let extracted = root
                .apply_step(step.clone())
                .expect("the alpha-equivalent antecedent should discharge the implication");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 48 * logarithmic_height + 192;
            assert!(
                allocations <= allocation_bound,
                "size {size} implication extract allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert_eq!(extracted.certificate().steps(), &[step]);
            assert_eq!(extracted.added_facts(), std::slice::from_ref(&target));
            assert!(extracted.is_complete());

            let missing_antecedent = Proof::for_pure_goal(
                "missing implication antecedent",
                std::slice::from_ref(&selected_implication),
                target.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            assert!(
                missing_antecedent
                    .apply_step(SimpleProofStep::Extract(target_surface.clone()))
                    .is_err(),
                "an indexed consequent does not bypass its antecedent"
            );
            assert!(missing_antecedent.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_instantiate_uses_indexed_universal_and_only_named_guards() {
        let parsed_function = syntax::parse_function("int32 selected(int32 x) { return x; }")
            .expect("test function should parse");
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let x_value = CValue::Int32(Bitvector32Term::Variable(Variable(8_700_000)));
        let arguments = vec![CExpression::Value(x_value)];
        let value = |constant| ContractExpression::CFragment(CExpression::Value(int32(constant)));
        let variable =
            |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
        let premise = ClickProposition::Comparison {
            left: variable("x"),
            operator: ComparisonOperator::LessEqual,
            right: value(7),
        };
        let goal_surface = ClickProposition::Comparison {
            left: value(7),
            operator: ComparisonOperator::Equal,
            right: value(7),
        };
        let quantified_surface = ClickProposition::ForAll {
            c_type: C0Type::Int32,
            name: "k".to_string(),
            body: Box::new(ClickProposition::Implies(
                Box::new(ClickProposition::Comparison {
                    left: variable("x"),
                    operator: ComparisonOperator::LessEqual,
                    right: variable("k"),
                }),
                Box::new(ClickProposition::Comparison {
                    left: variable("k"),
                    operator: ComparisonOperator::Equal,
                    right: variable("k"),
                }),
            )),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("test proposition should lower")
        };
        let kernel_premise = lower(&premise);
        let kernel_goal = lower(&goal_surface);
        let kernel_quantified = lower(&quantified_surface);

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
            available.push(kernel_premise.clone());
            available.push(kernel_quantified.clone());
            let root = Proof::for_point_goal(
                "indexed instantiate",
                0,
                &available,
                kernel_goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let key = quantified_replay_index_key(&kernel_quantified)
                .expect("the selected universal should have an alpha key");
            assert_eq!(
                root.facts()
                    .by_quantified_replay
                    .get(&key)
                    .expect("the selected universal should be indexed")
                    .len(),
                1,
                "unrelated facts must not enter the selected universal bucket"
            );

            let omitted = SimpleProofStep::InstantiateUsing {
                quantified: quantified_surface.clone(),
                argument: value(7),
                premises: Vec::new(),
            };
            assert!(
                root.apply_step(omitted).is_err(),
                "ambient availability must not discharge an omitted guard"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let step = SimpleProofStep::InstantiateUsing {
                quantified: quantified_surface.clone(),
                argument: value(7),
                premises: vec![premise.clone()],
            };
            let before = fact_node_allocations();
            let instantiated = root
                .apply_step(step.clone())
                .expect("the indexed universal and named guard should instantiate");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 48 * logarithmic_height + 192;
            assert!(
                allocations <= allocation_bound,
                "size {size} instantiate allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(instantiated.is_complete());
            assert_eq!(instantiated.certificate().steps(), &[step]);
            assert_eq!(
                instantiated.added_facts(),
                std::slice::from_ref(&kernel_goal)
            );
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn execution_apply_uses_only_named_evidence_and_forks_persistently() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test theorem and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let state = CState::new();
        let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_000_000)));
        let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_000_001)));
        let arguments = vec![CExpression::Value(left.clone())];
        let premise = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let conclusion = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let kernel_premise = lower_point_proposition_with_assumptions(
            &premise,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the exact premise should lower");
        let kernel_conclusion = lower_point_proposition_with_assumptions(
            &conclusion,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the theorem conclusion should lower");
        let application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: vec![
                ContractExpression::CFragment(CExpression::Value(left)),
                ContractExpression::CFragment(CExpression::Value(right)),
            ],
        };
        let missing_application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: application.arguments.iter().cloned().rev().collect(),
        };
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(kernel_premise.clone());
            let mut replay = TacticReplayState::default();
            replay
                .surface_propositions
                .record_lowering(&premise, &kernel_premise)
                .expect("the selected premise spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "persistent theorem application",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            assert!(
                root.try_theorem_application(&missing_application)
                    .expect("missing execution theorem search should be a bounded miss")
                    .is_none(),
                "an unavailable execution theorem premise must not manufacture a descendant"
            );
            let before_query = fact_node_allocations();
            let selected = root
                .select_execution_theorem_application_step(&application)
                .expect("smart search should select one explicit indexed premise");
            assert_eq!(
                fact_node_allocations() - before_query,
                0,
                "size {size} execution theorem selection must not rebuild persistent fact indexes"
            );
            assert_eq!(
                selected,
                SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: vec![premise.clone()],
                }
            );
            let omitted = root
                .apply_step(SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: Vec::new(),
                })
                .err()
                .expect("ambient facts must not discharge an omitted named premise");
            assert!(
                omitted.message().contains("required exact fact"),
                "{omitted:?}"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let step = selected;
            let before = fact_node_allocations();
            let applied = root
                .apply_step(step.clone())
                .expect("the exact named premise should certify the application");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 32 * logarithmic_height + 128;
            assert!(
                allocations <= allocation_bound,
                "size {size} theorem application allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(applied.certificate().steps(), &[step.clone()]);
            assert_eq!(
                applied.added_facts(),
                std::slice::from_ref(&kernel_conclusion)
            );
            let root_execution = root.execution().expect("root execution state");
            let applied_execution = applied
                .execution()
                .expect("application successor execution state");
            assert!(
                root_execution
                    .state
                    .shares_storage_with(&applied_execution.state),
                "theorem application does not alter the C state"
            );
            assert!(
                root_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .len()
                    == 0
            );
            assert!(
                applied_execution
                    .replay
                    .function_entry_execution_prerequisites
                    .contains(&kernel_conclusion)
            );
            assert_eq!(
                applied_execution
                    .last_step_delta
                    .function_entry_prerequisites,
                vec![kernel_conclusion.clone()]
            );
            assert_eq!(
                applied_execution
                    .last_step_delta
                    .function_entry_derivations
                    .len(),
                1
            );
            let alternative = root
                .apply_step(step)
                .expect("the retained ancestor should support another checked descendant");
            assert_eq!(alternative.certificate(), applied.certificate());
            assert!(root.certificate().steps().is_empty());
            let result = applied
                .into_execution_context()
                .expect("the checked successor should export at the compatibility boundary");
            assert!(result.pure_facts.contains(&kernel_conclusion));
        }
    }

    #[test]
    fn branch_theorem_search_retains_checked_arm_steps_and_scales() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 choose(int32 left, int32 right, int32 choose_left) {
                    immutable;
                    ensures reflexive_result: result == result by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function = syntax::parse_function(
            "int32 choose(int32 left, int32 right, int32 choose_left) { if (choose_left != 0) { return left; } else { return right; } }",
        )
        .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let state = CState::new();
        let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_050_000)));
        let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_050_001)));
        let choose_left = CValue::Int32(Bitvector32Term::Variable(Variable(8_050_002)));
        let arguments = vec![
            CExpression::Value(left.clone()),
            CExpression::Value(right.clone()),
            CExpression::Value(choose_left),
        ];
        let premise = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let unavailable_frame_premise = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(right.clone())),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(left.clone())),
        };
        let kernel_premise = lower_point_proposition_with_assumptions(
            &premise,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the exact theorem premise should lower");
        let application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: vec![
                ContractExpression::CFragment(CExpression::Value(left)),
                ContractExpression::CFragment(CExpression::Value(right)),
            ],
        };
        let missing_application = TheoremApplication {
            name: application.name.clone(),
            arguments: application.arguments.iter().cloned().rev().collect(),
        };

        let mut samples = Vec::new();
        let mut nested_samples = Vec::new();
        let mut execute_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(kernel_premise.clone());
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "choose".to_string(),
                    claim: CProofClaim::Grouped,
                }),
                ..TacticReplayState::default()
            };
            replay
                .surface_propositions
                .record_lowering(&premise, &kernel_premise)
                .expect("the selected premise spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "branch theorem search",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let branches = root
                .begin_execution_branch()
                .expect("the symbolic condition should expose two theorem-search arms");
            let nested_branches = branches.clone();
            let execute_branches = branches.clone();
            assert!(
                branches
                    .try_theorem_application(true, &missing_application)
                    .expect("an unavailable exact theorem premise should be a bounded miss")
                    .is_none(),
                "an unavailable theorem premise must not manufacture an arm descendant"
            );
            assert!(
                branches
                    .arm(true)
                    .expect("then arm remains feasible")
                    .certificate()
                    .steps()
                    .is_empty(),
                "failed theorem search must not alter arm provenance"
            );

            let before = fact_node_allocations();
            let branches = branches
                .try_theorem_application(true, &application)
                .expect("then arm theorem search should run")
                .expect("then arm theorem search should retain its checked step")
                .try_theorem_application(false, &application)
                .expect("else arm theorem search should run")
                .expect("else arm theorem search should retain its checked step");
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            for take_then in [true, false] {
                assert!(matches!(
                    branches
                        .arm(take_then)
                        .expect("both theorem-search arms remain feasible")
                        .certificate()
                        .steps(),
                    [SimpleProofStep::ApplyTheoremUsing {
                        application: retained,
                        premises,
                    }] if retained == &application && premises == std::slice::from_ref(&premise)
                ));
            }

            if size == 16 {
                let foreign = nested_branches
                    .begin_have(true, premise.clone())
                    .expect("the then arm should open a proposition proof")
                    .apply_step(SimpleProofStep::Assumption)
                    .expect("the root premise should close the nested arm proof");
                let rejected = match nested_branches.join_nested(false, foreign) {
                    Ok(_) => panic!("a nested proof from the then arm must not enter the else arm"),
                    Err(error) => error,
                };
                assert!(
                    rejected.message().contains("not rooted at the selected"),
                    "{rejected:?}"
                );
                for take_then in [true, false] {
                    assert!(
                        nested_branches
                            .arm(take_then)
                            .expect("both nested-proof arms remain feasible")
                            .certificate()
                            .steps()
                            .is_empty(),
                        "a rejected cross-arm join must not alter either arm"
                    );
                }
            }

            let before_nested = fact_node_allocations();
            let then_nested = nested_branches
                .begin_have(true, premise.clone())
                .expect("the then arm should open a proposition proof")
                .apply_step(SimpleProofStep::Assumption)
                .expect("the root premise should close the then-arm proof");
            let nested_branches = nested_branches
                .join_nested(true, then_nested)
                .expect("the completed proof should advance the then arm");
            let else_nested = nested_branches
                .begin_have(false, premise.clone())
                .expect("the else arm should open a proposition proof")
                .apply_step(SimpleProofStep::Assumption)
                .expect("the root premise should close the else-arm proof");
            let nested_branches = nested_branches
                .join_nested(false, else_nested)
                .expect("the completed proof should advance the else arm");
            nested_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before_nested,
            ));
            for take_then in [true, false] {
                assert!(matches!(
                    nested_branches
                        .arm(take_then)
                        .expect("both nested-proof arms remain feasible")
                        .certificate()
                        .steps(),
                    [SimpleProofStep::Have {
                        proposition: retained,
                        proof,
                    }] if retained == &premise
                        && proof.steps() == [SimpleProofStep::Assumption]
                ));
            }

            let before_execute = fact_node_allocations();
            let execute_branches = execute_branches
                .try_execute_arm_to_exit(true)
                .expect("then-arm execution search should run")
                .expect("the direct then return should produce a checked descendant")
                .try_execute_arm_to_exit(false)
                .expect("else-arm execution search should run")
                .expect("the direct else return should produce a checked descendant");
            for take_then in [true, false] {
                assert!(matches!(
                    execute_branches
                        .arm(take_then)
                        .expect("both terminal execution arms remain feasible")
                        .certificate()
                        .steps(),
                    [SimpleProofStep::StepUsing(premises)] if premises.len() == 1
                ));
            }
            let terminal = execute_branches
                .join_terminal()
                .expect("the two checked return arms should join as terminal outcomes");
            assert!(matches!(
                terminal.certificate().steps(),
                [SimpleProofStep::If {
                    then_proof,
                    else_proof,
                    ..
                }] if then_proof.steps().len() == 2 && else_proof.steps().len() == 2
            ));
            if size == 16 {
                let retained = terminal.clone();
                assert!(
                    terminal
                        .apply_step_at(
                            SimpleProofStep::FrameUsing {
                                region: None,
                                premises: vec![unavailable_frame_premise.clone()],
                            },
                            1,
                            1,
                        )
                        .is_err(),
                    "an unavailable frame premise must reject the checked descendant"
                );
                assert!(Arc::ptr_eq(&terminal.state, &retained.state));
                assert_eq!(terminal.certificate(), retained.certificate());
            }
            let framed = terminal
                .try_smart_frame_at(None, 1, 1)
                .expect("terminal frame search should run")
                .expect("the immutable effect should produce a checked frame descendant");
            execute_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before_execute,
            ));
            assert!(matches!(
                framed.certificate().steps(),
                [
                    SimpleProofStep::If { .. },
                    SimpleProofStep::FrameUsing {
                        region: None,
                        premises,
                    },
                ] if premises.is_empty()
            ));
            assert!(root.certificate().steps().is_empty());
        }
        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let bound = base_allocations + 96 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} two-arm theorem search allocated {allocations} persistent nodes (bound {bound})"
            );
        }
        let (_, base_height, base_allocations) = nested_samples[0];
        for (size, height, allocations) in nested_samples {
            let bound = base_allocations + 96 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} two-arm nested proof allocated {allocations} persistent nodes (bound {bound})"
            );
        }
        let (_, base_height, base_allocations) = execute_samples[0];
        for (size, height, allocations) in execute_samples {
            let bound = base_allocations + 128 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} two-arm terminal execution and frame allocated {allocations} persistent nodes (bound {bound})"
            );
        }
    }

    #[test]
    fn point_apply_search_uses_indexes_and_retains_its_checked_successor() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let state = CState::new();
        let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_100_000)));
        let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_100_001)));
        let arguments = vec![CExpression::Value(left.clone())];
        let premise = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let conclusion = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let program_point_states = ProgramPointStates::new();
        let kernel_premise = lower_point_proposition_with_assumptions(
            &premise,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the exact premise should lower");
        let kernel_conclusion = lower_point_proposition_with_assumptions(
            &conclusion,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the theorem conclusion should lower");
        let application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: vec![
                ContractExpression::CFragment(CExpression::Value(left)),
                ContractExpression::CFragment(CExpression::Value(right)),
            ],
        };
        let missing_application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: application.arguments.iter().cloned().rev().collect(),
        };
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&premise, &kernel_premise)
            .expect("the selected premise spelling should be recorded");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(Proposition::And(
                Box::new(kernel_premise.clone()),
                Box::new(indexed_fact(size + 10_000)),
            ));
            let goal = Proposition::And(
                Box::new(kernel_conclusion.clone()),
                Box::new(kernel_premise.clone()),
            );
            let root = Proof::for_point_goal(
                "persistent point theorem search",
                0,
                &facts,
                goal,
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let extracted = root
                .apply_step(SimpleProofStep::Extract(premise.clone()))
                .expect("a checked predecessor should promote the indexed conjunct");
            assert!(
                extracted
                    .try_theorem_application(&missing_application)
                    .expect("missing point theorem search should be a bounded miss")
                    .is_none(),
                "an unavailable point theorem premise must not manufacture a descendant"
            );
            let before_query = fact_node_allocations();
            let step = extracted
                .select_point_theorem_application_step(&application)
                .expect("smart search should select one explicit indexed premise");
            let query_allocations = fact_node_allocations() - before_query;
            assert_eq!(
                query_allocations, 0,
                "size {size} theorem selection must not rebuild persistent fact indexes"
            );
            assert_eq!(
                step,
                SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: vec![premise.clone()],
                }
            );
            let tactics = [
                ProofTactic::Extract(premise.clone()),
                ProofTactic::ApplyTheorem(application.clone()),
                ProofTactic::Simp,
            ];
            let before_apply = fact_node_allocations();
            let complete = root
                .try_linear_smart_script(&tactics)
                .expect("mixed linear search should not fail")
                .expect("extract, smart apply, and simp should close the goal");
            let allocations = fact_node_allocations() - before_apply;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 64 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} mixed point script allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(complete.is_complete());
            assert_eq!(
                complete.certificate().steps().first(),
                Some(&SimpleProofStep::Extract(premise.clone()))
            );
            assert_eq!(complete.certificate().steps().get(1), Some(&step));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn result_aware_point_apply_scales_with_unrelated_facts() {
        let click_file = crate::lang::click::parse(
            r#"
                theorem result_reflexive(value: int32) {
                    ensures value == value by { normalize(); }
                }

                int32 identity(int32 x) {
                    ensures result == x;
                } by {
                    execute();
                    have result == result by {
                        apply(result_reflexive(result));
                        simp();
                    }
                    simp();
                }
            "#,
        )
        .expect("result-aware theorem application should parse");
        let function_block = &click_file.function_blocks()[0];
        let SourceProof::Script(grouped_tactics) = function_block
            .grouped_proof()
            .expect("test function should have a grouped proof")
        else {
            panic!("test function should have a proof script");
        };
        let have = grouped_tactics
            .iter()
            .find_map(|tactic| match tactic {
                ProofTactic::Have(have) => Some(have),
                _ => None,
            })
            .expect("grouped proof should contain the result-aware have");
        let SourceProof::Script(have_tactics) = &have.proof else {
            panic!("result-aware have should contain a proof script");
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_150_000)),
        ))];
        let result = CValue::Int32(Bitvector32Term::Variable(Variable(8_150_001)));
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let surface_propositions = SurfacePropositionMap::default();
        let kernel_goal = lower_point_proposition_with_assumptions(
            &have.proposition,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the result-aware goal should lower");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let root = Proof::for_point_goal_with_requirements(
                "persistent result-aware theorem search",
                0,
                &facts,
                kernel_goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                Some(&result),
                None,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
                function_block.requires(),
                function_block.requirement_label_indices(),
            );
            let before = fact_node_allocations();
            let complete = root
                .try_linear_smart_script(have_tactics)
                .expect("result-aware theorem search should not fail")
                .expect("result-aware theorem application and simp should close the goal");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 64 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} result-aware point script allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(complete.is_complete());
            assert!(matches!(
                complete.certificate().steps().first(),
                Some(SimpleProofStep::ApplyTheoremUsing { application, premises })
                    if application.name == "result_reflexive" && premises.is_empty()
            ));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn result_aware_point_frontier_apply_is_indexed_and_transactional() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 bounded(int32 upper) {
                    ensures result <= upper;
                } by {
                    execute();
                    apply(int32_lt_implies_le(result, upper)) using {
                        result < upper;
                    }
                    simp();
                }
            "#,
        )
        .expect("result-aware explicit application should parse");
        let function_block = &click_file.function_blocks()[0];
        let SourceProof::Script(tactics) = function_block
            .grouped_proof()
            .expect("test function should have a grouped proof")
        else {
            panic!("test function should have a proof script");
        };
        let (application, surface_premise) = tactics
            .iter()
            .find_map(|tactic| match tactic {
                ProofTactic::ApplyTheoremUsing {
                    application,
                    premises,
                } => Some((application, premises.first()?)),
                _ => None,
            })
            .expect("grouped proof should contain an explicit theorem application");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("int32 bounded(int32 upper) { return upper; }")
                .expect("test C function should parse");
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(8_155_001)),
        ))];
        let result = CValue::Int32(Bitvector32Term::Variable(Variable(8_155_000)));
        let state = CState::new();
        let program_point_states = ProgramPointStates::new();
        let kernel_premise = lower_point_proposition_with_assumptions(
            surface_premise,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            Some(&result),
            &program_point_states,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the result-aware theorem premise should lower");
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(surface_premise, &kernel_premise)
            .expect("the selected premise spelling should be recorded");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(kernel_premise.clone());
            let root = Proof::for_point_frontier(
                "persistent result-aware outcome apply",
                0,
                &facts,
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                Some(&result),
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let missing = root
                .apply_step(SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: Vec::new(),
                })
                .err()
                .expect("ambient availability must not discharge an omitted premise");
            assert!(missing.message().contains("required exact fact"));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let before_query = fact_node_allocations();
            let step = root
                .select_point_theorem_application_step(application)
                .expect("the indexed result-aware premise should be selected");
            assert_eq!(fact_node_allocations() - before_query, 0);
            assert_eq!(
                step,
                SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: vec![surface_premise.clone()],
                }
            );
            let before_apply = fact_node_allocations();
            let applied = root
                .apply_step(step.clone())
                .expect("the selected result-aware theorem step should check");
            let allocations = fact_node_allocations() - before_apply;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 64 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} result-aware frontier apply allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(!applied.is_complete());
            assert_eq!(applied.certificate().steps(), &[step]);
            assert_eq!(applied.added_facts().len(), 1);
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_transport_can_follow_another_checked_step() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let source = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(8_160_000)),
            ))),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(8_160_001)),
            ))),
        };
        let extracted = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(8_160_002)),
            ))),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(8_160_003)),
            ))),
        };
        let missing = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(8_160_006)),
            ))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(8_160_007)),
            ))),
        };
        let program_point_states = ProgramPointStates::new();
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &[],
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("test proposition should lower")
        };
        let kernel_source = lower(&source);
        let kernel_extracted = lower(&extracted);
        let surface_propositions = SurfacePropositionMap::default();
        let result = int32(0);
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(kernel_source.clone());
            facts.push(Proposition::And(
                Box::new(kernel_extracted.clone()),
                Box::new(indexed_fact(8_160_004)),
            ));
            let root = Proof::for_point_frontier(
                "nested result-aware point transport",
                0,
                &facts,
                parsed_function.parameters(),
                &[],
                &state,
                &state,
                Some(&result),
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let refined = root
                .apply_step(SimpleProofStep::Extract(extracted.clone()))
                .expect("the predecessor should advance the proof");
            let retained_refined = refined.clone();
            let rejected = refined.apply_step(SimpleProofStep::TransportUsing {
                source: source.clone(),
                target: missing.clone(),
                premises: Vec::new(),
            });
            assert!(rejected.is_err());
            assert!(Arc::ptr_eq(&refined.state, &retained_refined.state));

            let transport = SimpleProofStep::TransportUsing {
                source: source.clone(),
                target: source.clone(),
                premises: Vec::new(),
            };
            let before = fact_node_allocations();
            let transported = refined
                .apply_step(transport.clone())
                .expect("the exact ambient source should occupy its own checked slot");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 16 * logarithmic_height + 64;
            assert!(
                allocations <= allocation_bound,
                "size {size} point transport allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                transported.certificate().steps(),
                &[SimpleProofStep::Extract(extracted.clone()), transport,]
            );
            assert_eq!(transported.added_facts(), &[]);
            assert_eq!(root.certificate().steps(), &[]);
        }
    }

    #[test]
    fn pure_signed_order_simp_builds_its_theorem_path_with_logarithmic_local_updates() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions =
            combined_theorem_definitions(&click_file).expect("standard order theorems should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let memory = CMemory::new();
        let terms = [
            Bitvector32Term::Variable(Variable(8_150_000)),
            Bitvector32Term::Variable(Variable(8_150_001)),
            Bitvector32Term::Variable(Variable(8_150_002)),
            Bitvector32Term::Variable(Variable(8_150_003)),
        ];
        let expression = |term: &Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
        };
        let comparison = |left: usize, operator, right: usize| ClickProposition::Comparison {
            left: expression(&terms[left]),
            operator,
            right: expression(&terms[right]),
        };
        let surfaces = vec![
            comparison(0, ComparisonOperator::LessEqual, 1),
            comparison(1, ComparisonOperator::LessThan, 2),
            comparison(2, ComparisonOperator::LessEqual, 3),
        ];
        let surface_goal = comparison(0, ComparisonOperator::LessThan, 3);
        let lower = |surface: &ClickProposition| {
            lower_pure_theorem_proposition(
                "persistent signed-order simp",
                surface,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &memory,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed signed comparison should lower")
        };
        let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
        let goal = lower(&surface_goal);
        let mut surface_requirements = SurfacePropositionMap::default();
        for (kernel, surface) in premises.iter().zip(&surfaces) {
            surface_requirements
                .record_lowering(surface, kernel)
                .expect("the exact requirement spelling should be indexed");
        }

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.extend(premises.iter().cloned());
            let theorem_context = PureTheoremContext {
                memory: memory.clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: requires.clone(),
                surface_requirements: surface_requirements.clone(),
            };
            let root = Proof::for_pure_goal(
                "persistent signed-order simp",
                &requires,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed path should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 128 * logarithmic_height + 512;
            assert!(
                allocations <= allocation_bound,
                "size {size} signed-order simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [
                    SimpleProofStep::Have { .. },
                    SimpleProofStep::ApplyTheoremUsing { .. },
                    SimpleProofStep::Assumption
                ]
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn pure_equality_refinement_simp_applies_one_rewrite_with_logarithmic_local_updates() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let memory = CMemory::new();
        let value = Bitvector32Term::Variable(Variable(8_174_000));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let equality = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(Bitvector32Term::Constant(1)),
        };
        let goal_surface = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessEqual,
            right: expression(Bitvector32Term::Subtract(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(1)),
            )),
        };
        let lower = |surface: &ClickProposition| {
            lower_pure_theorem_proposition(
                "persistent equality-refinement simp",
                surface,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &memory,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed int32 proposition should lower")
        };
        let kernel_equality = lower(&equality);
        let goal = lower(&goal_surface);
        let mut surface_requirements = SurfacePropositionMap::default();
        surface_requirements
            .record_lowering(&equality, &kernel_equality)
            .expect("the exact equality spelling should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.push(kernel_equality.clone());
            let theorem_context = PureTheoremContext {
                memory: memory.clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: requires.clone(),
                surface_requirements: surface_requirements.clone(),
            };
            let root = Proof::for_pure_goal(
                "persistent equality-refinement simp",
                &requires,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("one selected equality should refine and close the Proof");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 64 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} equality-refinement simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::Rewrite(_), SimpleProofStep::Normalize]
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_predecessor_simp_builds_checked_scope_with_logarithmic_local_updates() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let value = Bitvector32Term::Variable(Variable(8_174_100));
        let upper = Bitvector32Term::Variable(Variable(8_174_101));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let equality = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(Bitvector32Term::Constant(1)),
        };
        let upper_bound = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessEqual,
            right: expression(upper.clone()),
        };
        let goal_surface = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Subtract(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            operator: ComparisonOperator::LessEqual,
            right: expression(upper),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed point proposition should lower")
        };
        let kernel_equality = lower(&equality);
        let kernel_upper_bound = lower(&upper_bound);
        let goal = lower(&goal_surface);
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&equality, &kernel_equality)
            .expect("the exact equality spelling should be indexed");
        surface_propositions
            .record_lowering(&upper_bound, &kernel_upper_bound)
            .expect("the exact upper-bound spelling should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(kernel_equality.clone());
            facts.push(kernel_upper_bound.clone());
            let root = Proof::for_point_goal(
                "persistent point predecessor simp",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the predecessor search should retain one structured descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 128 * logarithmic_height + 512;
            assert!(
                allocations <= allocation_bound,
                "size {size} point predecessor simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [
                    SimpleProofStep::Have { .. },
                    SimpleProofStep::ApplyTheoremUsing { .. }
                ]
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_equality_simp_builds_its_recorded_path_with_logarithmic_local_updates() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let terms = [
            Bitvector32Term::Variable(Variable(8_175_000)),
            Bitvector32Term::Variable(Variable(8_175_001)),
            Bitvector32Term::Variable(Variable(8_175_002)),
            Bitvector32Term::Variable(Variable(8_175_003)),
        ];
        let expression = |term: &Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
        };
        let equal = |left: usize, right: usize| ClickProposition::Comparison {
            left: expression(&terms[left]),
            operator: ComparisonOperator::Equal,
            right: expression(&terms[right]),
        };
        let surfaces = vec![equal(1, 0), equal(1, 2), equal(2, 3)];
        let surface_goal = equal(0, 3);
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed equality should lower")
        };
        let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
        let goal = lower(&surface_goal);
        let mut surface_propositions = SurfacePropositionMap::default();
        for (kernel, surface) in premises.iter().zip(&surfaces) {
            surface_propositions
                .record_lowering(surface, kernel)
                .expect("the exact point spelling should be indexed");
        }

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend(premises.iter().cloned());
            let root = Proof::for_point_goal(
                "persistent point equality simp",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed equality path should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 128 * logarithmic_height + 512;
            assert!(
                allocations <= allocation_bound,
                "size {size} point equality simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [
                    SimpleProofStep::Rewrite(_),
                    SimpleProofStep::Rewrite(_),
                    SimpleProofStep::Rewrite(_),
                    SimpleProofStep::Normalize,
                ]
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_order_simp_builds_its_theorem_path_with_logarithmic_local_updates() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions =
            combined_theorem_definitions(&click_file).expect("standard order theorems should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let terms = [
            Bitvector32Term::Variable(Variable(8_176_000)),
            Bitvector32Term::Variable(Variable(8_176_001)),
            Bitvector32Term::Variable(Variable(8_176_002)),
            Bitvector32Term::Variable(Variable(8_176_003)),
        ];
        let expression = |term: &Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term.clone())))
        };
        let comparison = |left: usize, operator, right: usize| ClickProposition::Comparison {
            left: expression(&terms[left]),
            operator,
            right: expression(&terms[right]),
        };
        let surfaces = vec![
            comparison(0, ComparisonOperator::LessEqual, 1),
            comparison(1, ComparisonOperator::LessThan, 2),
            comparison(2, ComparisonOperator::LessEqual, 3),
        ];
        let surface_goal = comparison(0, ComparisonOperator::LessThan, 3);
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed signed comparison should lower")
        };
        let premises = surfaces.iter().map(lower).collect::<Vec<_>>();
        let goal = lower(&surface_goal);
        let mut surface_propositions = SurfacePropositionMap::default();
        for (kernel, surface) in premises.iter().zip(&surfaces) {
            surface_propositions
                .record_lowering(surface, kernel)
                .expect("the exact point spelling should be indexed");
        }

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend(premises.iter().cloned());
            let root = Proof::for_point_goal(
                "persistent point order simp",
                0,
                &facts,
                goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed order path should build one checked point Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 128 * logarithmic_height + 512;
            assert!(
                allocations <= allocation_bound,
                "size {size} point order simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [
                    SimpleProofStep::Have { proof, .. },
                    SimpleProofStep::ApplyTheoremUsing { .. },
                ] if matches!(
                    proof.steps(),
                    [SimpleProofStep::ApplyTheoremUsing { .. }]
                )
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn point_single_premise_arithmetic_simps_retain_indexed_theorem_steps() {
        #[derive(Clone, Copy)]
        enum ArithmeticProofShape {
            Direct,
            ComposedNegatedSuccessor,
            ChainedIncrementUpper,
        }

        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard increment theorem should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let value = Bitvector32Term::Variable(Variable(8_177_000));
        let upper = Bitvector32Term::Variable(Variable(8_177_001));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let premise = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(upper.clone()),
        };
        let definedness_premise = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(Bitvector32Term::Constant(i32::MAX as u32)),
        };
        let positive_premise = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(1)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let strictly_positive_premise = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessThan,
            right: expression(value.clone()),
        };
        let successor_lower_premise = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(2)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let strong_constant_lower_premise = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(3)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let negated_successor_premise =
            ClickProposition::Not(Box::new(ClickProposition::Comparison {
                left: expression(value.clone()),
                operator: ComparisonOperator::LessThan,
                right: expression(Bitvector32Term::Constant(2)),
            }));
        let increment_constant_upper_premise = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessEqual,
            right: expression(Bitvector32Term::Constant(3)),
        };
        let increment_constant_upper_intermediate = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(Bitvector32Term::Constant(5)),
        };
        let surface_bound_goal = ClickProposition::Comparison {
            left: ContractExpression::Add(
                Box::new(expression(value.clone())),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            ),
            operator: ComparisonOperator::LessEqual,
            right: expression(upper.clone()),
        };
        let surface_strict_goal = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Add(
                Box::new(expression(value.clone())),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            ),
        };
        let surface_defined_goal = ClickProposition::Defined {
            expression: ContractExpression::Add(
                Box::new(expression(value.clone())),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            ),
        };
        let surface_one_plus_defined_goal = ClickProposition::Defined {
            expression: ContractExpression::Add(
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
                Box::new(expression(value.clone())),
            ),
        };
        let surface_one_plus_strict_goal = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Add(
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
                Box::new(expression(value.clone())),
            ),
        };
        let surface_nonnegative_goal = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let surface_nonnegative_ge_goal = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::GreaterEqual,
            right: expression(Bitvector32Term::Constant(0)),
        };
        let surface_successor_lower_goal = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::GreaterEqual,
            right: expression(Bitvector32Term::Constant(1)),
        };
        let surface_adjacent_strict_goal = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(1)),
            operator: ComparisonOperator::LessThan,
            right: expression(value.clone()),
        };
        let surface_increment_constant_upper_goal = ClickProposition::Comparison {
            left: ContractExpression::Add(
                Box::new(expression(value.clone())),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            ),
            operator: ComparisonOperator::LessEqual,
            right: expression(Bitvector32Term::Constant(5)),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed increment proposition should lower")
        };
        let kernel_premise = lower(&premise);
        let kernel_definedness_premise = lower(&definedness_premise);
        let kernel_positive_premise = lower(&positive_premise);
        let kernel_strictly_positive_premise = lower(&strictly_positive_premise);
        let kernel_successor_lower_premise = lower(&successor_lower_premise);
        let kernel_strong_constant_lower_premise = lower(&strong_constant_lower_premise);
        let kernel_negated_successor_premise = lower(&negated_successor_premise);
        let kernel_increment_constant_upper_premise = lower(&increment_constant_upper_premise);
        let goals = [
            (
                lower(&surface_bound_goal),
                "int32_increment_upper_bound",
                "increment bound",
                &premise,
                &kernel_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_strict_goal),
                "int32_increment_strictly_increases",
                "strict increment",
                &premise,
                &kernel_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_defined_goal),
                "int32_increment_below_max_is_defined",
                "increment definedness",
                &definedness_premise,
                &kernel_definedness_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_one_plus_defined_goal),
                "int32_one_plus_below_max_is_defined",
                "one-plus definedness",
                &definedness_premise,
                &kernel_definedness_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_one_plus_strict_goal),
                "int32_one_plus_strictly_increases",
                "one-plus strict increase",
                &definedness_premise,
                &kernel_definedness_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_nonnegative_goal),
                "int32_positive_is_nonnegative",
                "positive to nonnegative",
                &positive_premise,
                &kernel_positive_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_nonnegative_ge_goal),
                "int32_strictly_positive_is_nonnegative",
                "strictly positive to nonnegative",
                &strictly_positive_premise,
                &kernel_strictly_positive_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_adjacent_strict_goal),
                "int32_successor_le_implies_lt",
                "adjacent strict lower bound",
                &successor_lower_premise,
                &kernel_successor_lower_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_nonnegative_goal),
                "int32_le_transitive",
                "constant lower-bound weakening",
                &strong_constant_lower_premise,
                &kernel_strong_constant_lower_premise,
                ArithmeticProofShape::Direct,
            ),
            (
                lower(&surface_successor_lower_goal),
                "int32_ge_transitive",
                "negated strict successor bound",
                &negated_successor_premise,
                &kernel_negated_successor_premise,
                ArithmeticProofShape::ComposedNegatedSuccessor,
            ),
            (
                lower(&surface_increment_constant_upper_goal),
                "int32_increment_upper_bound",
                "increment under a larger constant",
                &increment_constant_upper_premise,
                &kernel_increment_constant_upper_premise,
                ArithmeticProofShape::ChainedIncrementUpper,
            ),
        ];
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&premise, &kernel_premise)
            .expect("the exact strict premise should be indexed");
        surface_propositions
            .record_lowering(&definedness_premise, &kernel_definedness_premise)
            .expect("the exact maximum premise should be indexed");
        surface_propositions
            .record_lowering(&positive_premise, &kernel_positive_premise)
            .expect("the exact positive premise should be indexed");
        surface_propositions
            .record_lowering(&successor_lower_premise, &kernel_successor_lower_premise)
            .expect("the exact successor lower-bound premise should be indexed");
        surface_propositions
            .record_lowering(
                &strong_constant_lower_premise,
                &kernel_strong_constant_lower_premise,
            )
            .expect("the exact stronger constant lower bound should be indexed");
        surface_propositions
            .record_lowering(
                &strictly_positive_premise,
                &kernel_strictly_positive_premise,
            )
            .expect("the exact strictly-positive premise should be indexed");
        surface_propositions
            .record_lowering(
                &negated_successor_premise,
                &kernel_negated_successor_premise,
            )
            .expect("the exact negated successor premise should be indexed");
        surface_propositions
            .record_lowering(
                &increment_constant_upper_premise,
                &kernel_increment_constant_upper_premise,
            )
            .expect("the exact constant upper-bound premise should be indexed");

        for (goal, theorem_name, label, surface_premise, kernel_premise, shape) in goals {
            for size in [16_u32, 64, 256, 1024, 4096] {
                let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
                facts.push(kernel_premise.clone());
                let root = Proof::for_point_goal(
                    "persistent point increment-bound simp",
                    0,
                    &facts,
                    goal.clone(),
                    parsed_function.parameters(),
                    &arguments,
                    &state,
                    &state,
                    &program_point_states,
                    &surface_propositions,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                    &[],
                    &[],
                );
                let retained_root = root.clone();
                let before = fact_node_allocations();
                let closed = root
                    .try_simp_closure()
                    .expect("smart search must not exceed its deadline")
                    .expect("the typed increment rule should build one checked Proof descendant");
                let allocations = fact_node_allocations() - before;
                let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
                let allocation_bound = match shape {
                    ArithmeticProofShape::Direct => 64 * logarithmic_height + 256,
                    ArithmeticProofShape::ComposedNegatedSuccessor
                    | ArithmeticProofShape::ChainedIncrementUpper => 96 * logarithmic_height + 384,
                };
                assert!(
                    allocations <= allocation_bound,
                    "size {size} point {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(closed.is_complete());
                match shape {
                    ArithmeticProofShape::Direct => assert!(
                        matches!(
                            closed.certificate().steps(),
                            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                                if application.name == theorem_name
                                    && premises == std::slice::from_ref(surface_premise)
                        ),
                        "{label} retained unexpected point steps: {:#?}",
                        closed.certificate().steps()
                    ),
                    ArithmeticProofShape::ComposedNegatedSuccessor => assert!(matches!(
                        closed.certificate().steps(),
                        [
                            SimpleProofStep::Have { proof: first, .. },
                            SimpleProofStep::Have { proof: second, .. },
                            SimpleProofStep::ApplyTheoremUsing { application, .. },
                        ] if matches!(
                            first.steps(),
                            [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                                if application.name == "int32_not_lt_implies_ge"
                                    && premises == std::slice::from_ref(surface_premise)
                        ) && matches!(second.steps(), [SimpleProofStep::Normalize])
                            && application.name == theorem_name
                    )),
                    ArithmeticProofShape::ChainedIncrementUpper => assert!(matches!(
                        closed.certificate().steps(),
                        [
                            SimpleProofStep::ApplyTheoremUsing {
                                application: first,
                                premises: first_premises,
                            },
                            SimpleProofStep::ApplyTheoremUsing {
                                application: second,
                                premises: second_premises,
                            },
                        ] if first.name == "int32_le_lt_transitive"
                            && first_premises == std::slice::from_ref(surface_premise)
                            && second.name == theorem_name
                            && second_premises
                                == std::slice::from_ref(&increment_constant_upper_intermediate)
                    )),
                }
                assert!(Arc::ptr_eq(&root.state, &retained_root.state));
                assert!(root.certificate().steps().is_empty());

                let theorem_context = PureTheoremContext {
                    memory: state.memory().clone(),
                    values: BTreeMap::new(),
                    array_refs: BTreeMap::new(),
                    requires: facts.clone(),
                    surface_requirements: surface_propositions.clone(),
                };
                let pure_root = Proof::for_pure_goal(
                    "persistent restricted increment-bound simp",
                    &facts,
                    goal.clone(),
                    &theorem_context,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                );
                let retained_pure_root = pure_root.clone();
                assert!(
                    pure_root.try_restricted_simp_closure(&[]).is_none(),
                    "omitting the named premise must reject the restricted candidate"
                );
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                let before_restricted = fact_node_allocations();
                let pure_closed = pure_root
                    .try_restricted_simp_closure(std::slice::from_ref(surface_premise))
                    .unwrap_or_else(|| {
                        panic!("restricted simp should retain the checked typed {label} rule")
                    });
                let restricted_allocations = fact_node_allocations() - before_restricted;
                assert!(
                    restricted_allocations <= allocation_bound,
                    "size {size} restricted {label} simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(pure_closed.is_complete());
                match shape {
                    ArithmeticProofShape::Direct => assert!(matches!(
                        pure_closed.certificate().steps(),
                        [
                            SimpleProofStep::ApplyTheoremUsing { application, premises },
                            SimpleProofStep::Assumption,
                        ] if application.name == theorem_name
                            && premises == std::slice::from_ref(surface_premise)
                    )),
                    ArithmeticProofShape::ComposedNegatedSuccessor => assert!(matches!(
                        pure_closed.certificate().steps(),
                        [
                            SimpleProofStep::Have { proof: first, .. },
                            SimpleProofStep::Have { proof: second, .. },
                            SimpleProofStep::ApplyTheoremUsing { application, .. },
                            SimpleProofStep::Assumption,
                        ] if matches!(
                            first.steps(),
                            [
                                SimpleProofStep::ApplyTheoremUsing { application, premises },
                                SimpleProofStep::Assumption,
                            ] if application.name == "int32_not_lt_implies_ge"
                                && premises == std::slice::from_ref(surface_premise)
                        ) && matches!(second.steps(), [SimpleProofStep::Normalize])
                            && application.name == theorem_name
                    )),
                    ArithmeticProofShape::ChainedIncrementUpper => assert!(matches!(
                        pure_closed.certificate().steps(),
                        [
                            SimpleProofStep::ApplyTheoremUsing {
                                application: first,
                                premises: first_premises,
                            },
                            SimpleProofStep::ApplyTheoremUsing {
                                application: second,
                                premises: second_premises,
                            },
                            SimpleProofStep::Assumption,
                        ] if first.name == "int32_le_lt_transitive"
                            && first_premises == std::slice::from_ref(surface_premise)
                            && second.name == theorem_name
                            && second_premises
                                == std::slice::from_ref(&increment_constant_upper_intermediate)
                    )),
                }
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                assert!(pure_root.certificate().steps().is_empty());
            }
        }
    }

    #[test]
    fn increment_bound_family_retains_two_indexed_theorem_premises() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard increment theorem should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let lower = Bitvector32Term::Variable(Variable(8_178_000));
        let value = Bitvector32Term::Variable(Variable(8_178_001));
        let upper = Bitvector32Term::Variable(Variable(8_178_002));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let lower_premise = ClickProposition::Comparison {
            left: expression(lower.clone()),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let upper_premise = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(upper.clone()),
        };
        let increment = |term: Bitvector32Term| {
            ContractExpression::Add(
                Box::new(expression(term)),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            )
        };
        let surface_goals = [
            (
                ClickProposition::Comparison {
                    left: expression(lower.clone()),
                    operator: ComparisonOperator::LessEqual,
                    right: increment(value.clone()),
                },
                "int32_increment_lower_bound",
                "less-equal lower bound",
            ),
            (
                ClickProposition::Comparison {
                    left: increment(value.clone()),
                    operator: ComparisonOperator::GreaterEqual,
                    right: expression(lower.clone()),
                },
                "int32_increment_greater_equal_lower_bound",
                "greater-equal lower bound",
            ),
            (
                ClickProposition::Comparison {
                    left: increment(value.clone()),
                    operator: ComparisonOperator::GreaterThan,
                    right: expression(lower.clone()),
                },
                "int32_increment_strict_greater_lower_bound",
                "strict-greater lower bound",
            ),
            (
                ClickProposition::Comparison {
                    left: increment(lower.clone()),
                    operator: ComparisonOperator::LessEqual,
                    right: increment(value.clone()),
                },
                "int32_increment_preserves_order",
                "incremented order",
            ),
        ];
        let lower_surface = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed increment-lower-bound proposition should lower")
        };
        let kernel_lower = lower_surface(&lower_premise);
        let kernel_upper = lower_surface(&upper_premise);
        let goals = surface_goals
            .iter()
            .map(|(surface, theorem, label)| (lower_surface(surface), *theorem, *label))
            .collect::<Vec<_>>();
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&lower_premise, &kernel_lower)
            .expect("the exact lower premise should be indexed");
        surface_propositions
            .record_lowering(&upper_premise, &kernel_upper)
            .expect("the exact upper premise should be indexed");
        let selected_premises = [lower_premise.clone(), upper_premise.clone()];

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend([kernel_lower.clone(), kernel_upper.clone()]);
            for (goal, theorem_name, label) in &goals {
                let root = Proof::for_point_goal(
                    "persistent point increment-bound-family simp",
                    0,
                    &facts,
                    goal.clone(),
                    parsed_function.parameters(),
                    &arguments,
                    &state,
                    &state,
                    &program_point_states,
                    &surface_propositions,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                    &[],
                    &[],
                );
                let retained_root = root.clone();
                let before = fact_node_allocations();
                let closed = root
                    .try_simp_closure()
                    .expect("smart search must not exceed its deadline")
                    .expect("the typed two-premise rule should build one checked Proof descendant");
                let allocations = fact_node_allocations() - before;
                let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
                let allocation_bound = 96 * logarithmic_height + 384;
                assert!(
                    allocations <= allocation_bound,
                    "size {size} point {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(closed.is_complete());
                assert!(matches!(
                    closed.certificate().steps(),
                    [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                        if application.name == *theorem_name
                            && premises.as_slice() == selected_premises
                ));
                assert!(Arc::ptr_eq(&root.state, &retained_root.state));
                assert!(root.certificate().steps().is_empty());

                let theorem_context = PureTheoremContext {
                    memory: state.memory().clone(),
                    values: BTreeMap::new(),
                    array_refs: BTreeMap::new(),
                    requires: facts.clone(),
                    surface_requirements: surface_propositions.clone(),
                };
                let pure_root = Proof::for_pure_goal(
                    "persistent restricted increment-bound-family simp",
                    &facts,
                    goal.clone(),
                    &theorem_context,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                );
                let retained_pure_root = pure_root.clone();
                for omitted in [
                    std::slice::from_ref(&lower_premise),
                    std::slice::from_ref(&upper_premise),
                ] {
                    assert!(
                        pure_root.try_restricted_simp_closure(omitted).is_none(),
                        "omitting either theorem premise must reject the restricted candidate"
                    );
                    assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                }
                let before_restricted = fact_node_allocations();
                let pure_closed = pure_root
                    .try_restricted_simp_closure(&selected_premises)
                    .expect("restricted simp should retain the checked two-premise rule");
                let restricted_allocations = fact_node_allocations() - before_restricted;
                assert!(
                    restricted_allocations <= allocation_bound,
                    "size {size} restricted {label} simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(pure_closed.is_complete());
                assert!(matches!(
                    pure_closed.certificate().steps(),
                    [
                        SimpleProofStep::ApplyTheoremUsing { application, premises },
                        SimpleProofStep::Assumption,
                    ] if application.name == *theorem_name
                        && premises.as_slice() == selected_premises
                ));
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                assert!(pure_root.certificate().steps().is_empty());
            }
        }

        let strict_lower_premise = ClickProposition::Comparison {
            left: expression(lower.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(value.clone()),
        };
        let strict_goal_surface = ClickProposition::Comparison {
            left: increment(value.clone()),
            operator: ComparisonOperator::GreaterThan,
            right: expression(lower.clone()),
        };
        let kernel_strict_lower = lower_surface(&strict_lower_premise);
        let strict_goal = lower_surface(&strict_goal_surface);
        let mut strict_surface_propositions = SurfacePropositionMap::default();
        strict_surface_propositions
            .record_lowering(&strict_lower_premise, &kernel_strict_lower)
            .expect("the exact strict lower premise should be indexed");
        strict_surface_propositions
            .record_lowering(&upper_premise, &kernel_upper)
            .expect("the exact upper premise should be indexed");
        let strict_selected_premises = [strict_lower_premise.clone(), upper_premise.clone()];

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend([kernel_strict_lower.clone(), kernel_upper.clone()]);
            let root = Proof::for_point_goal(
                "persistent point strict increment-bound simp",
                0,
                &facts,
                strict_goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &strict_surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the strict-lower increment path should advance one Proof");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point strict-lower simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [
                    SimpleProofStep::ApplyTheoremUsing { application: first, premises: first_premises },
                    SimpleProofStep::ApplyTheoremUsing { application: second, premises: second_premises },
                ] if first.name == "int32_lt_implies_le"
                    && first_premises == std::slice::from_ref(&strict_lower_premise)
                    && second.name == "int32_increment_strict_greater_lower_bound"
                    && second_premises.len() == 2
                    && second_premises[1] == upper_premise
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let theorem_context = PureTheoremContext {
                memory: state.memory().clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: facts.clone(),
                surface_requirements: strict_surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted strict increment-bound simp",
                &facts,
                strict_goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted in [
                std::slice::from_ref(&strict_lower_premise),
                std::slice::from_ref(&upper_premise),
            ] {
                assert!(pure_root.try_restricted_simp_closure(omitted).is_none());
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            }
            let before_restricted = fact_node_allocations();
            let pure_closed = pure_root
                .try_restricted_simp_closure(&strict_selected_premises)
                .expect("restricted strict-lower simp should advance one Proof");
            let restricted_allocations = fact_node_allocations() - before_restricted;
            assert!(
                restricted_allocations <= allocation_bound,
                "size {size} restricted strict-lower simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(pure_closed.is_complete());
            assert!(matches!(
                pure_closed.certificate().steps(),
                [
                    SimpleProofStep::ApplyTheoremUsing { application: first, .. },
                    SimpleProofStep::ApplyTheoremUsing { application: second, .. },
                    SimpleProofStep::Assumption,
                ] if first.name == "int32_lt_implies_le"
                    && second.name == "int32_increment_strict_greater_lower_bound"
            ));
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            assert!(pure_root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn le_and_not_lt_equality_simp_retains_one_indexed_theorem_application() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard equality theorem should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let left = Bitvector32Term::Variable(Variable(8_178_100));
        let right = Bitvector32Term::Variable(Variable(8_178_101));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let less_equal = ClickProposition::Comparison {
            left: expression(left.clone()),
            operator: ComparisonOperator::LessEqual,
            right: expression(right.clone()),
        };
        let not_less_than = ClickProposition::Not(Box::new(ClickProposition::Comparison {
            left: expression(left.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(right.clone()),
        }));
        let equality = ClickProposition::Comparison {
            left: expression(left),
            operator: ComparisonOperator::Equal,
            right: expression(right),
        };
        let lower_surface = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed equality proposition should lower")
        };
        let kernel_less_equal = lower_surface(&less_equal);
        let kernel_not_less_than = lower_surface(&not_less_than);
        let kernel_equality = lower_surface(&equality);
        let selected = [less_equal.clone(), not_less_than.clone()];
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&less_equal, &kernel_less_equal)
            .expect("the <= premise should be indexed");
        surface_propositions
            .record_lowering(&not_less_than, &kernel_not_less_than)
            .expect("the not-< premise should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend([kernel_less_equal.clone(), kernel_not_less_than.clone()]);
            let root = Proof::for_point_goal(
                "persistent point <=/not-< equality simp",
                0,
                &facts,
                kernel_equality.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed equality rule should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point equality simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                    if application.name == "int32_le_and_not_lt_implies_eq"
                        && premises.as_slice() == selected
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let restricted_kernels = selected
                .iter()
                .map(|surface| {
                    lower_pure_theorem_proposition(
                        "persistent restricted <=/not-< equality simp",
                        surface,
                        &BTreeMap::new(),
                        &BTreeMap::new(),
                        state.memory(),
                        &predicate_environment,
                        &click_function_environment,
                    )
                    .expect("each restricted equality premise should lower")
                })
                .collect::<Vec<_>>();
            assert_eq!(restricted_kernels[0], kernel_less_equal);
            assert!(condition_polarity_equivalent(
                &restricted_kernels[1],
                &kernel_not_less_than
            ));
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.extend(restricted_kernels.iter().cloned());
            let theorem_context = PureTheoremContext {
                memory: state.memory().clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: pure_facts.clone(),
                surface_requirements: surface_propositions.clone(),
            };
            let pure_root = Proof::for_pure_goal(
                "persistent restricted <=/not-< equality simp",
                &pure_facts,
                kernel_equality.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_pure_root = pure_root.clone();
            for omitted in [
                std::slice::from_ref(&less_equal),
                std::slice::from_ref(&not_less_than),
            ] {
                assert!(pure_root.try_restricted_simp_closure(omitted).is_none());
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
            }
            let restricted_derivation = plan_simp_certificate(
                &kernel_equality,
                &assumptions_from_propositions(&restricted_kernels),
            )
            .expect("the restricted equality facts should produce a derivation");
            let SimpEvidence::Derivation(restricted_derivation) = restricted_derivation else {
                panic!("the equality rule should be contextual")
            };
            assert!(
                restricted_derivation
                    .int32_le_and_not_lt_implies_equality_premises()
                    .is_some(),
                "the restricted derivation should retain the named equality rule"
            );
            let restricted_pairs = restricted_kernels
                .iter()
                .cloned()
                .zip(selected.iter().cloned())
                .collect::<Vec<_>>();
            let recorded = recorded_int32_le_and_not_lt_implies_equality_pairs(
                &restricted_derivation,
                &restricted_pairs,
            )
            .expect("the typed equality evidence should recover both Surface premises");
            let planned = plan_recorded_int32_le_and_not_lt_implies_equality_for_context(
                &kernel_equality,
                &recorded,
                false,
            )
            .expect("the typed equality evidence should select the named theorem");
            let planned_certificate = ProofCertificate::from_proof_tactics(&planned)
                .expect("the named equality theorem should form a simple certificate");
            pure_root
                .check_certificate(&planned_certificate)
                .unwrap_or_else(|error| panic!("the named equality certificate failed: {error:?}"));
            let pure_closed = pure_root
                .try_restricted_simp_closure(&selected)
                .expect("restricted simp should retain the checked equality theorem");
            assert!(matches!(
                pure_closed.certificate().steps(),
                [
                    SimpleProofStep::ApplyTheoremUsing { application, premises },
                    SimpleProofStep::Assumption,
                ] if application.name == "int32_le_and_not_lt_implies_eq"
                    && premises.as_slice() == selected
            ));
            assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
        }
    }

    #[test]
    fn ge_and_not_gt_equality_simp_retains_one_indexed_theorem_application() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard equality theorem should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let left = Bitvector32Term::Variable(Variable(8_178_102));
        let right = Bitvector32Term::Variable(Variable(8_178_103));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let greater_equal = ClickProposition::Comparison {
            left: expression(left.clone()),
            operator: ComparisonOperator::GreaterEqual,
            right: expression(right.clone()),
        };
        let not_greater_than = ClickProposition::Not(Box::new(ClickProposition::Comparison {
            left: expression(left.clone()),
            operator: ComparisonOperator::GreaterThan,
            right: expression(right.clone()),
        }));
        let equality = ClickProposition::Comparison {
            left: expression(left),
            operator: ComparisonOperator::Equal,
            right: expression(right),
        };
        let lower_surface = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed equality proposition should lower")
        };
        let kernel_greater_equal = lower_surface(&greater_equal);
        let kernel_not_greater_than = lower_surface(&not_greater_than);
        let kernel_equality = lower_surface(&equality);
        let selected = [greater_equal.clone(), not_greater_than.clone()];
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&greater_equal, &kernel_greater_equal)
            .expect("the >= premise should be indexed");
        surface_propositions
            .record_lowering(&not_greater_than, &kernel_not_greater_than)
            .expect("the not-> premise should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend([
                kernel_greater_equal.clone(),
                kernel_not_greater_than.clone(),
            ]);
            let root = Proof::for_point_goal(
                "persistent point >=/not-> equality simp",
                0,
                &facts,
                kernel_equality.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed >=/not-> rule should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point >=/not-> equality simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                    if application.name == "int32_ge_and_not_gt_implies_eq"
                        && premises.as_slice() == selected
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn le_and_neq_strict_simp_retains_one_indexed_theorem_application() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard strict-order theorem should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let left = Bitvector32Term::Variable(Variable(8_178_104));
        let right = Bitvector32Term::Variable(Variable(8_178_105));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let less_equal = ClickProposition::Comparison {
            left: expression(left.clone()),
            operator: ComparisonOperator::LessEqual,
            right: expression(right.clone()),
        };
        let not_equal = ClickProposition::Not(Box::new(ClickProposition::Comparison {
            left: expression(left.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(right.clone()),
        }));
        let strict = ClickProposition::Comparison {
            left: expression(left),
            operator: ComparisonOperator::LessThan,
            right: expression(right),
        };
        let lower_surface = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed strict-order proposition should lower")
        };
        let kernel_less_equal = lower_surface(&less_equal);
        let kernel_not_equal = lower_surface(&not_equal);
        let kernel_strict = lower_surface(&strict);
        let selected = [less_equal.clone(), not_equal.clone()];
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&less_equal, &kernel_less_equal)
            .expect("the <= premise should be indexed");
        surface_propositions
            .record_lowering(&not_equal, &kernel_not_equal)
            .expect("the != premise should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.extend([kernel_less_equal.clone(), kernel_not_equal.clone()]);
            let root = Proof::for_point_goal(
                "persistent point <=/!= strict-order simp",
                0,
                &facts,
                kernel_strict.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the typed <=/!= rule should build one checked Proof descendant");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 384;
            assert!(
                allocations <= allocation_bound,
                "size {size} point <=/!= strict-order simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                    if application.name == "int32_le_and_neq_implies_lt"
                        && premises.as_slice() == selected
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn symbolic_arithmetic_definedness_retains_two_indexed_theorem_premises() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard symbolic-add theorem should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let value = Bitvector32Term::Variable(Variable(8_178_100));
        let amount = Bitvector32Term::Variable(Variable(8_178_101));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let amount_nonnegative = ClickProposition::Comparison {
            left: expression(amount.clone()),
            operator: ComparisonOperator::GreaterEqual,
            right: expression(Bitvector32Term::Constant(0)),
        };
        let headroom = ContractExpression::Subtract(
            Box::new(expression(Bitvector32Term::Constant(i32::MAX as u32))),
            Box::new(expression(amount.clone())),
        );
        let within_headroom = ClickProposition::Comparison {
            left: headroom,
            operator: ComparisonOperator::GreaterEqual,
            right: expression(value.clone()),
        };
        let within_value = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::GreaterEqual,
            right: expression(amount.clone()),
        };
        let surface_add_goal = ClickProposition::Defined {
            expression: ContractExpression::Add(
                Box::new(expression(value.clone())),
                Box::new(expression(amount.clone())),
            ),
        };
        let surface_subtract_goal = ClickProposition::Defined {
            expression: ContractExpression::Subtract(
                Box::new(expression(value.clone())),
                Box::new(expression(amount.clone())),
            ),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the symbolic arithmetic proposition should lower")
        };
        let kernel_nonnegative = lower(&amount_nonnegative);
        let kernel_headroom = lower(&within_headroom);
        let kernel_within_value = lower(&within_value);
        let cases = [
            (
                lower(&surface_add_goal),
                "int32_nonnegative_add_within_max_is_defined",
                [amount_nonnegative.clone(), within_headroom.clone()],
                [kernel_nonnegative.clone(), kernel_headroom.clone()],
                "symbolic-add",
            ),
            (
                lower(&surface_subtract_goal),
                "int32_nonnegative_subtract_within_value_is_defined",
                [amount_nonnegative.clone(), within_value.clone()],
                [kernel_nonnegative.clone(), kernel_within_value.clone()],
                "symbolic-subtract",
            ),
        ];
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&amount_nonnegative, &kernel_nonnegative)
            .expect("the exact nonnegative premise should be indexed");
        surface_propositions
            .record_lowering(&within_headroom, &kernel_headroom)
            .expect("the exact headroom premise should be indexed");
        surface_propositions
            .record_lowering(&within_value, &kernel_within_value)
            .expect("the exact within-value premise should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            for (kernel_goal, theorem_name, selected, kernel_premises, label) in &cases {
                let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
                facts.extend(kernel_premises.iter().cloned());
                let root = Proof::for_point_goal(
                    "persistent point symbolic arithmetic simp",
                    0,
                    &facts,
                    kernel_goal.clone(),
                    parsed_function.parameters(),
                    &arguments,
                    &state,
                    &state,
                    &program_point_states,
                    &surface_propositions,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                    &[],
                    &[],
                );
                let retained_root = root.clone();
                let before = fact_node_allocations();
                let closed = root
                    .try_simp_closure()
                    .expect("smart search must not exceed its deadline")
                    .expect(
                    "the typed symbolic arithmetic rule should build one checked Proof descendant",
                );
                let allocations = fact_node_allocations() - before;
                let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
                let allocation_bound = 96 * logarithmic_height + 384;
                assert!(
                    allocations <= allocation_bound,
                    "size {size} point {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(closed.is_complete());
                assert!(matches!(
                    closed.certificate().steps(),
                    [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                            if application.name == *theorem_name
                                && premises.as_slice() == selected
                ));
                assert!(Arc::ptr_eq(&root.state, &retained_root.state));
                assert!(root.certificate().steps().is_empty());

                let theorem_context = PureTheoremContext {
                    memory: state.memory().clone(),
                    values: BTreeMap::new(),
                    array_refs: BTreeMap::new(),
                    requires: facts.clone(),
                    surface_requirements: surface_propositions.clone(),
                };
                let pure_root = Proof::for_pure_goal(
                    "persistent restricted symbolic arithmetic simp",
                    &facts,
                    kernel_goal.clone(),
                    &theorem_context,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                );
                let retained_pure_root = pure_root.clone();
                for omitted in [
                    std::slice::from_ref(&selected[0]),
                    std::slice::from_ref(&selected[1]),
                ] {
                    assert!(pure_root.try_restricted_simp_closure(omitted).is_none());
                    assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                }
                let before_restricted = fact_node_allocations();
                let pure_closed = pure_root
                    .try_restricted_simp_closure(selected)
                    .expect("restricted simp should retain the symbolic arithmetic theorem");
                let restricted_allocations = fact_node_allocations() - before_restricted;
                assert!(
                    restricted_allocations <= allocation_bound,
                    "size {size} restricted {label} simp allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(matches!(
                    pure_closed.certificate().steps(),
                    [
                        SimpleProofStep::ApplyTheoremUsing { application, premises },
                        SimpleProofStep::Assumption,
                        ] if application.name == *theorem_name
                            && premises.as_slice() == selected
                ));
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                assert!(pure_root.certificate().steps().is_empty());
            }
        }
    }

    #[test]
    fn selected_disjunction_simp_retains_checked_cases_and_scales() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let value = Bitvector32Term::Variable(Variable(8_178_900));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let equal_zero = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(Bitvector32Term::Constant(0)),
        };
        let equal_one = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(Bitvector32Term::Constant(1)),
        };
        let disjunction =
            ClickProposition::Or(Box::new(equal_zero.clone()), Box::new(equal_one.clone()));
        let surface_goal = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value),
        };
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed proposition should lower")
        };
        let kernel_disjunction = lower(&disjunction);
        let kernel_goal = lower(&surface_goal);
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&disjunction, &kernel_disjunction)
            .expect("the selected disjunction should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(kernel_disjunction.clone());
            let root = Proof::for_point_goal(
                "persistent point disjunction simp",
                0,
                &facts,
                kernel_goal.clone(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                &program_point_states,
                &surface_propositions,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
                &[],
                &[],
            );
            assert_eq!(
                root.facts().assumptions().disjunction_fact_count(),
                1,
                "unrelated facts must not enter the disjunction candidate index"
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .try_simp_closure()
                .expect("smart search must not exceed its deadline")
                .expect("the selected disjunction should close both checked Proof arms");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 160 * logarithmic_height + 640;
            assert!(
                allocations <= allocation_bound,
                "size {size} disjunction simp allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(closed.is_complete());
            assert!(matches!(
                closed.certificate().steps(),
                [SimpleProofStep::Cases {
                    disjunction: retained,
                    left_proof,
                    right_proof,
                }] if retained == &disjunction
                    && matches!(
                        left_proof.steps(),
                        [SimpleProofStep::Rewrite(equality), SimpleProofStep::Normalize]
                            if equality == &equal_zero
                    )
                    && matches!(
                        right_proof.steps(),
                        [SimpleProofStep::Rewrite(equality), SimpleProofStep::Normalize]
                            if equality == &equal_one
                    )
            ));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn surface_structural_simp_retains_recursive_child_proofs_and_scales() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let left_value = Bitvector32Term::Variable(Variable(8_178_910));
        let right_value = Bitvector32Term::Variable(Variable(8_178_911));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let left_positive = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(1)),
            operator: ComparisonOperator::LessEqual,
            right: expression(left_value.clone()),
        };
        let right_positive = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(1)),
            operator: ComparisonOperator::LessEqual,
            right: expression(right_value.clone()),
        };
        let left_nonnegative = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessEqual,
            right: expression(left_value.clone()),
        };
        let right_nonnegative = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessEqual,
            right: expression(right_value.clone()),
        };
        let branch_condition = ClickProposition::Comparison {
            left: expression(left_value.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(right_value),
        };
        let negative = ClickProposition::Comparison {
            left: expression(left_value.clone()),
            operator: ComparisonOperator::LessThan,
            right: expression(Bitvector32Term::Constant(0)),
        };
        let reflexive = ClickProposition::Comparison {
            left: expression(left_value.clone()),
            operator: ComparisonOperator::Equal,
            right: expression(left_value),
        };
        let conjunction = ClickProposition::And(
            Box::new(left_nonnegative.clone()),
            Box::new(right_nonnegative),
        );
        let disjunction =
            ClickProposition::Or(Box::new(left_nonnegative.clone()), Box::new(negative));
        let implication =
            ClickProposition::Implies(Box::new(reflexive), Box::new(left_positive.clone()));
        let lower = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed structural proposition should lower")
        };
        let kernel_left_positive = lower(&left_positive);
        let kernel_right_positive = lower(&right_positive);
        let mut surface_propositions = SurfacePropositionMap::default();
        surface_propositions
            .record_lowering(&left_positive, &kernel_left_positive)
            .expect("the recursive left premise should be indexed");
        surface_propositions
            .record_lowering(&right_positive, &kernel_right_positive)
            .expect("the recursive right premise should be indexed");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let unrelated = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 256 * logarithmic_height + 1024;
            for (label, surface_goal, selected_facts) in [
                (
                    "conjunction",
                    &conjunction,
                    &[kernel_left_positive.clone(), kernel_right_positive.clone()][..],
                ),
                (
                    "disjunction",
                    &disjunction,
                    std::slice::from_ref(&kernel_left_positive),
                ),
                (
                    "implication",
                    &implication,
                    std::slice::from_ref(&kernel_left_positive),
                ),
            ] {
                let mut facts = unrelated.clone();
                facts.extend_from_slice(selected_facts);
                let root = Proof::for_point_surface_goal(
                    "persistent surface structural simp",
                    0,
                    &facts,
                    lower(surface_goal),
                    surface_goal.clone(),
                    parsed_function.parameters(),
                    &arguments,
                    &state,
                    &state,
                    &program_point_states,
                    &surface_propositions,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                    &[],
                    &[],
                );
                let retained_root = root.clone();
                let Some(Goal::Proposition(root_goal)) = root.sole_goal() else {
                    unreachable!("the structural regression owns a proposition goal")
                };
                let root_surface = root_goal
                    .surface
                    .as_ref()
                    .expect("the root should own its exact Surface goal");
                let branches = root
                    .begin_if(branch_condition.clone())
                    .expect("an unrelated condition should fork the structural goal");
                for arm in &branches.arms {
                    let Some(Goal::Proposition(arm_goal)) = arm.sole_goal() else {
                        unreachable!("a pure proof branch retains its proposition goal")
                    };
                    assert!(Arc::ptr_eq(
                        root_surface,
                        arm_goal
                            .surface
                            .as_ref()
                            .expect("the branch should share the root Surface goal")
                    ));
                }
                let before = fact_node_allocations();
                let closed = root
                    .try_simp_closure()
                    .expect("smart search must not exceed its deadline")
                    .unwrap_or_else(|| panic!("the {label} should retain its recursive proof"));
                let allocations = fact_node_allocations() - before;
                assert!(
                    allocations <= allocation_bound,
                    "size {size} {label} simp allocated {allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(closed.is_complete());
                let retained_steps = closed.certificate();
                match label {
                    "conjunction" => assert!(
                        matches!(
                            retained_steps.steps(),
                            [
                                SimpleProofStep::Have { proof: left, .. },
                                SimpleProofStep::Have { proof: right, .. },
                                SimpleProofStep::Split,
                            ] if matches!(
                                left.steps(),
                                [SimpleProofStep::ApplyTheoremUsing { .. }]
                            ) && matches!(
                                right.steps(),
                                [SimpleProofStep::ApplyTheoremUsing { .. }]
                            )
                        ),
                        "{retained_steps:#?}"
                    ),
                    "disjunction" => assert!(
                        matches!(
                            retained_steps.steps(),
                            [
                                SimpleProofStep::Have { proof, .. },
                                SimpleProofStep::Left,
                            ] if matches!(
                                proof.steps(),
                                [SimpleProofStep::ApplyTheoremUsing { .. }]
                            )
                        ),
                        "{retained_steps:#?}"
                    ),
                    "implication" => assert!(
                        matches!(
                            retained_steps.steps(),
                            [SimpleProofStep::Intro, SimpleProofStep::Assumption,]
                        ),
                        "{retained_steps:#?}"
                    ),
                    _ => unreachable!(),
                }
                assert!(Arc::ptr_eq(&root.state, &retained_root.state));
                assert!(root.certificate().steps().is_empty());
            }
        }
    }

    #[test]
    fn predecessor_simps_retain_indexed_named_rule_premises() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("the standard predecessor theorems should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let parsed_function =
            syntax::parse_function("void noop() {}").expect("test C function should parse");
        let state = CState::new();
        let arguments = Vec::new();
        let program_point_states = ProgramPointStates::new();
        let value = Bitvector32Term::Variable(Variable(8_179_000));
        let bound = Bitvector32Term::Variable(Variable(8_179_001));
        let expression = |term: Bitvector32Term| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(term)))
        };
        let predecessor = || {
            ContractExpression::Subtract(
                Box::new(expression(value.clone())),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            )
        };
        let positive = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessThan,
            right: expression(value.clone()),
        };
        let nonnegative = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(0)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let bounded = ClickProposition::Comparison {
            left: expression(value.clone()),
            operator: ComparisonOperator::LessEqual,
            right: expression(bound.clone()),
        };
        let one_le = ClickProposition::Comparison {
            left: expression(Bitvector32Term::Constant(1)),
            operator: ComparisonOperator::LessEqual,
            right: expression(value.clone()),
        };
        let surface_goals = [
            (
                ClickProposition::Comparison {
                    left: expression(Bitvector32Term::Constant(0)),
                    operator: ComparisonOperator::LessEqual,
                    right: predecessor(),
                },
                "int32_positive_predecessor_is_nonnegative",
                vec![positive.clone()],
                false,
            ),
            (
                ClickProposition::Comparison {
                    left: predecessor(),
                    operator: ComparisonOperator::LessThan,
                    right: expression(value.clone()),
                },
                "int32_positive_predecessor_strictly_decreases",
                vec![positive.clone()],
                false,
            ),
            (
                ClickProposition::Comparison {
                    left: predecessor(),
                    operator: ComparisonOperator::LessEqual,
                    right: expression(bound),
                },
                "int32_nonnegative_predecessor_upper_bound",
                vec![nonnegative.clone(), bounded.clone()],
                false,
            ),
            (
                ClickProposition::Comparison {
                    left: expression(Bitvector32Term::Constant(0)),
                    operator: ComparisonOperator::LessEqual,
                    right: predecessor(),
                },
                "int32_positive_predecessor_is_nonnegative",
                vec![one_le.clone()],
                true,
            ),
            (
                ClickProposition::Comparison {
                    left: predecessor(),
                    operator: ComparisonOperator::LessThan,
                    right: expression(value.clone()),
                },
                "int32_positive_predecessor_strictly_decreases",
                vec![one_le.clone()],
                true,
            ),
        ];
        let lower_surface = |surface: &ClickProposition| {
            lower_point_proposition_with_assumptions(
                surface,
                &PureFactContext::new(),
                parsed_function.parameters(),
                &arguments,
                &state,
                &state,
                None,
                &program_point_states,
                &predicate_environment,
                &click_function_environment,
            )
            .expect("the fixed predecessor proposition should lower")
        };
        let kernel_positive = lower_surface(&positive);
        let kernel_nonnegative = lower_surface(&nonnegative);
        let kernel_bounded = lower_surface(&bounded);
        let kernel_one_le = lower_surface(&one_le);
        let goals = surface_goals
            .iter()
            .map(|(surface, theorem, selected, nested)| {
                (lower_surface(surface), *theorem, selected.clone(), *nested)
            })
            .collect::<Vec<_>>();
        let mut surface_propositions = SurfacePropositionMap::default();
        for (surface, kernel) in [
            (&positive, &kernel_positive),
            (&nonnegative, &kernel_nonnegative),
            (&bounded, &kernel_bounded),
            (&one_le, &kernel_one_le),
        ] {
            surface_propositions
                .record_lowering(surface, kernel)
                .expect("each exact predecessor premise should be indexed");
        }

        for size in [16_u32, 64, 256, 1024, 4096] {
            let unrelated_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            for (goal, theorem_name, selected, nested) in &goals {
                let mut facts = unrelated_facts.clone();
                facts.extend(selected.iter().map(&lower_surface));
                let root = Proof::for_point_goal(
                    "persistent point predecessor simp",
                    0,
                    &facts,
                    goal.clone(),
                    parsed_function.parameters(),
                    &arguments,
                    &state,
                    &state,
                    &program_point_states,
                    &surface_propositions,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                    &[],
                    &[],
                );
                let retained_root = root.clone();
                let before = fact_node_allocations();
                let closed = root
                    .try_simp_closure()
                    .expect("smart search must not exceed its deadline")
                    .unwrap_or_else(|| {
                        panic!(
                            "the typed predecessor rule {theorem_name} (nested={nested}) should build a checked Proof descendant"
                        )
                    });
                let allocations = fact_node_allocations() - before;
                let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
                let allocation_bound = 96 * logarithmic_height + 384;
                assert!(
                    allocations <= allocation_bound,
                    "size {size} point {theorem_name} allocated {allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(closed.is_complete());
                if *nested {
                    assert!(matches!(
                        closed.certificate().steps(),
                        [
                            SimpleProofStep::Have { proof, .. },
                            SimpleProofStep::ApplyTheoremUsing { application, premises },
                        ] if application.name == *theorem_name
                            && premises.len() == 1
                            && matches!(
                                proof.steps(),
                                [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                                    if application.name == "int32_successor_le_implies_lt"
                                    && premises == selected
                            )
                    ));
                } else {
                    assert!(matches!(
                        closed.certificate().steps(),
                        [SimpleProofStep::ApplyTheoremUsing { application, premises }]
                            if application.name == *theorem_name && premises == selected
                    ));
                }
                assert!(Arc::ptr_eq(&root.state, &retained_root.state));
                assert!(root.certificate().steps().is_empty());

                let theorem_context = PureTheoremContext {
                    memory: state.memory().clone(),
                    values: BTreeMap::new(),
                    array_refs: BTreeMap::new(),
                    requires: facts.clone(),
                    surface_requirements: surface_propositions.clone(),
                };
                let pure_root = Proof::for_pure_goal(
                    "persistent restricted predecessor simp",
                    &facts,
                    goal.clone(),
                    &theorem_context,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                );
                let retained_pure_root = pure_root.clone();
                for omitted_index in 0..selected.len() {
                    let omitted = selected
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| *index != omitted_index)
                        .map(|(_, premise)| premise.clone())
                        .collect::<Vec<_>>();
                    assert!(
                        pure_root.try_restricted_simp_closure(&omitted).is_none(),
                        "omitting a theorem premise must reject the restricted candidate"
                    );
                    assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                }
                let before_restricted = fact_node_allocations();
                let pure_closed = pure_root
                    .try_restricted_simp_closure(selected)
                    .expect("restricted simp should retain the checked predecessor rule");
                let restricted_allocations = fact_node_allocations() - before_restricted;
                assert!(
                    restricted_allocations <= allocation_bound,
                    "size {size} restricted {theorem_name} allocated {restricted_allocations} persistent nodes (bound {allocation_bound})"
                );
                assert!(pure_closed.is_complete());
                if *nested {
                    assert!(matches!(
                        pure_closed.certificate().steps(),
                        [
                            SimpleProofStep::Have { proof, .. },
                            SimpleProofStep::ApplyTheoremUsing { application, premises },
                            SimpleProofStep::Assumption,
                        ] if application.name == *theorem_name
                            && premises.len() == 1
                            && matches!(
                                proof.steps(),
                                [
                                    SimpleProofStep::ApplyTheoremUsing { application, premises },
                                    SimpleProofStep::Assumption,
                                ] if application.name == "int32_successor_le_implies_lt"
                                    && premises == selected
                            )
                    ));
                } else {
                    assert!(matches!(
                        pure_closed.certificate().steps(),
                        [
                            SimpleProofStep::ApplyTheoremUsing { application, premises },
                            SimpleProofStep::Assumption,
                        ] if application.name == *theorem_name && premises == selected
                    ));
                }
                assert!(Arc::ptr_eq(&pure_root.state, &retained_pure_root.state));
                assert!(pure_root.certificate().steps().is_empty());
            }
        }
    }

    #[test]
    fn pure_apply_search_instantiates_requirements_and_retains_its_successor() {
        let click_file = crate::lang::click::parse("")
            .expect("an empty source should still admit the standard theorem prelude");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_definitions = combined_theorem_definitions(&click_file)
            .expect("standard theorem prelude should load");
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        let memory = CMemory::new();
        let left = CValue::Int32(Bitvector32Term::Variable(Variable(8_200_000)));
        let right = CValue::Int32(Bitvector32Term::Variable(Variable(8_200_001)));
        let premise = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let conclusion = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(left.clone())),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::CFragment(CExpression::Value(right.clone())),
        };
        let kernel_premise = lower_pure_theorem_proposition(
            "persistent pure theorem search",
            &premise,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the exact pure premise should lower");
        let kernel_conclusion = lower_pure_theorem_proposition(
            "persistent pure theorem search",
            &conclusion,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &memory,
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the pure theorem conclusion should lower");
        let application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: vec![
                ContractExpression::CFragment(CExpression::Value(left)),
                ContractExpression::CFragment(CExpression::Value(right)),
            ],
        };
        let missing_application = TheoremApplication {
            name: "int32_lt_implies_le".to_string(),
            arguments: application.arguments.iter().cloned().rev().collect(),
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            requires.push(kernel_premise.clone());
            let theorem_context = PureTheoremContext {
                memory: memory.clone(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires: requires.clone(),
                surface_requirements: SurfacePropositionMap::default(),
            };
            let goal = Proposition::And(
                Box::new(kernel_conclusion.clone()),
                Box::new(kernel_premise.clone()),
            );
            let root = Proof::for_pure_goal(
                "persistent pure theorem search",
                &requires,
                goal,
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            assert!(
                root.try_theorem_application(&missing_application)
                    .expect("missing pure theorem search should be a bounded miss")
                    .is_none(),
                "an unavailable pure theorem premise must not manufacture a descendant"
            );
            let missing = root
                .select_pure_theorem_application_step(&missing_application)
                .err()
                .expect("an unavailable instantiated requirement must reject the candidate");
            assert!(missing.message().contains("required exact fact"));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            let before_query = fact_node_allocations();
            let step = root
                .select_pure_theorem_application_step(&application)
                .expect("smart pure search should select the indexed source requirement");
            let query_allocations = fact_node_allocations() - before_query;
            assert_eq!(
                query_allocations, 0,
                "size {size} pure theorem selection must not rebuild persistent fact indexes"
            );
            assert_eq!(
                step,
                SimpleProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises: vec![premise.clone()],
                }
            );
            let before_script = fact_node_allocations();
            let complete = root
                .try_linear_smart_script(&[
                    ProofTactic::ApplyTheorem(application.clone()),
                    ProofTactic::Simp,
                ])
                .expect("linear pure search should not fail")
                .expect("the checked conclusion should close the conjunction");
            let script_allocations = fact_node_allocations() - before_script;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 64 * logarithmic_height + 256;
            assert!(
                script_allocations <= allocation_bound,
                "size {size} pure linear script allocated {script_allocations} persistent nodes (bound {allocation_bound})"
            );
            assert!(complete.is_complete());
            assert_eq!(complete.certificate().steps().first(), Some(&step));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
        }
    }

    #[test]
    fn execution_unfold_forks_persistently_and_ignores_unrelated_facts() {
        let click_file = crate::lang::click::parse(
            r#"
                predicate selected(x: int32) { x == x }
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test predicate and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(click_file.predicate_definitions());
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let state = CState::new();
        let argument = CExpression::Value(CValue::Int32(Bitvector32Term::Constant(7)));
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let arguments = vec![argument.clone()];
        let surface = ClickProposition::PredicateCall {
            name: "selected".to_string(),
            arguments: vec![ContractExpression::CFragment(argument)],
        };
        let predicate = Proposition::Predicate {
            name: "selected".to_string(),
            arguments: vec![
                Term::CState(state.clone()),
                Term::CValue(CValue::Int32(Bitvector32Term::Constant(7))),
            ],
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(predicate.clone());
            let mut replay = TacticReplayState::default();
            replay
                .surface_propositions
                .record_lowering(&surface, &predicate)
                .expect("the selected predicate spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "persistent unfold",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let successor = root
                .apply_step(SimpleProofStep::UnfoldPredicate("selected".to_string()))
                .expect("the exact selected predicate should unfold");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 32 * logarithmic_height + 128;
            assert!(
                allocations <= allocation_bound,
                "size {size} unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
            );

            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert_eq!(root.facts().to_vec().len(), size as usize + 1);
            assert_eq!(root.certificate().steps(), &[]);
            assert_eq!(
                successor.certificate().steps(),
                &[SimpleProofStep::UnfoldPredicate("selected".to_string())]
            );
            assert!(successor.facts().to_vec().len() > root.facts().to_vec().len());
            let root_execution = root.execution().expect("root execution state");
            let successor_execution = successor.execution().expect("successor execution state");
            assert!(
                root_execution
                    .state
                    .shares_storage_with(&successor_execution.state),
                "unfold does not alter the C frontier"
            );
            assert!(
                root_execution
                    .replay
                    .proof_certificate_builder
                    .shares_storage_with(&successor_execution.replay.proof_certificate_builder),
                "unfold does not copy unrelated certificate history"
            );
            assert!(
                root_execution
                    .replay
                    .effect_facts
                    .shares_storage_with(&successor_execution.replay.effect_facts),
                "unfold does not copy unrelated effect history"
            );

            let context = successor
                .into_execution_context()
                .expect("a sole successor should materialize its legacy boundary context");
            assert!(
                context
                    .replay
                    .unfolded_predicates
                    .contains(&"selected".to_string())
            );
            assert!(context.pure_facts.len() > size as usize + 1);
        }
    }

    #[test]
    fn execution_resource_observation_is_retained_transactional_and_logarithmic() {
        let click_file = crate::lang::click::parse(
            r#"
                resource marker(x: int32) {
                    fact x == x;
                }
                verifying "identity.c";
                int32 identity(int32 x) {
                    views marker(x);
                    immutable;
                    ensures returns_x: result == x;
                } by {
                    observe(marker(x));
                    execute();
                    frame();
                }
            "#,
        )
        .expect("test resource and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let resource = function_block
            .requires()
            .iter()
            .find_map(|requirement| match requirement.inner() {
                Requirement::Resource(resource) => Some(resource.clone()),
                _ => None,
            })
            .expect("the test function should require its marker view");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let empty_state = CState::new();
        let lowered = lower_resource_clause(
            &resource,
            parsed_function.parameters(),
            &arguments,
            empty_state.memory(),
        )
        .expect("the required marker view should lower");
        let state =
            empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

        for size in [16_u32, 64, 256, 1024, 4096] {
            let root = Proof::for_execution_frontier(
                "persistent resource observation",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay: TacticReplayState::default(),
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let observed = root
                .apply_step(SimpleProofStep::ObserveResource(resource.clone()))
                .expect("the held marker view should be observable");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} observation allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                observed.certificate().steps(),
                &[SimpleProofStep::ObserveResource(resource.clone())]
            );
            assert!(!observed.added_facts().is_empty());
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let mut missing = resource.clone();
            let ResourceClause::Declared { name, .. } = &mut missing else {
                panic!("the marker resource should be declared");
            };
            *name = "missing_marker".to_string();
            assert!(
                root.apply_step(SimpleProofStep::ObserveResource(missing))
                    .is_err()
            );
            assert!(root.certificate().steps().is_empty());
            assert_eq!(root.facts().to_vec().len(), size as usize);
        }
    }

    #[test]
    fn execution_resource_unfold_is_retained_transactional_and_logarithmic() {
        let click_file = crate::lang::click::parse(
            r#"
                resource marker(x: int32) {
                    fact x == x;
                }
                verifying "identity.c";
                int32 identity(int32 x) {
                    owns marker(x);
                    immutable;
                    ensures returns_x: result == x;
                } by {
                    unfold(marker(x));
                    execute();
                    frame();
                }
            "#,
        )
        .expect("test resource and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let resource = function_block
            .requires()
            .iter()
            .find_map(|requirement| match requirement.inner() {
                Requirement::Resource(resource) => Some(resource.clone()),
                _ => None,
            })
            .expect("the test function should own its marker resource");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let empty_state = CState::new();
        let lowered = lower_resource_clause(
            &resource,
            parsed_function.parameters(),
            &arguments,
            empty_state.memory(),
        )
        .expect("the owned marker resource should lower");
        let state =
            empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

        for size in [16_u32, 64, 256, 1024, 4096] {
            let root = Proof::for_execution_frontier(
                "persistent resource unfold",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay: TacticReplayState::default(),
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let unfolded = root
                .apply_step(SimpleProofStep::UnfoldResource(resource.clone()))
                .expect("the owned marker resource should unfold");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} unfold allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                unfolded.certificate().steps(),
                &[SimpleProofStep::UnfoldResource(resource.clone())]
            );
            assert!(!unfolded.added_facts().is_empty());
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let mut missing = resource.clone();
            let ResourceClause::Declared { name, .. } = &mut missing else {
                panic!("the marker resource should be declared");
            };
            *name = "missing_marker".to_string();
            assert!(
                root.apply_step(SimpleProofStep::UnfoldResource(missing))
                    .is_err()
            );
            assert!(root.certificate().steps().is_empty());
            assert_eq!(root.facts().to_vec().len(), size as usize);
        }
    }

    #[test]
    fn execution_resource_fold_is_retained_transactional_and_logarithmic() {
        let click_file = crate::lang::click::parse(
            r#"
                resource marker(x: int32) {
                    fact x == x;
                }
                verifying "identity.c";
                int32 identity(int32 x) {
                    owns marker(x);
                    immutable;
                    ensures returns_x: result == x;
                } by {
                    unfold(marker(x));
                    fold(marker(x));
                    execute();
                    frame();
                }
            "#,
        )
        .expect("test resource and function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let resource = function_block
            .requires()
            .iter()
            .find_map(|requirement| match requirement.inner() {
                Requirement::Resource(resource) => Some(resource.clone()),
                _ => None,
            })
            .expect("the test function should own its marker resource");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let empty_state = CState::new();
        let lowered = lower_resource_clause(
            &resource,
            parsed_function.parameters(),
            &arguments,
            empty_state.memory(),
        )
        .expect("the owned marker resource should lower");
        let state =
            empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));

        for size in [16_u32, 64, 256, 1024, 4096] {
            let root = Proof::for_execution_frontier(
                "persistent resource fold",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay: TacticReplayState::default(),
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let unfolded = root
                .apply_step(SimpleProofStep::UnfoldResource(resource.clone()))
                .expect("the owned marker resource should unfold before folding");
            let retained_unfolded = unfolded.clone();
            let before = fact_node_allocations();
            let folded = unfolded
                .apply_step(SimpleProofStep::FoldResource(resource.clone()))
                .expect("the exposed marker body should fold");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 96 * logarithmic_height + 256;
            assert!(
                allocations <= allocation_bound,
                "size {size} fold allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                folded.certificate().steps(),
                &[
                    SimpleProofStep::UnfoldResource(resource.clone()),
                    SimpleProofStep::FoldResource(resource.clone()),
                ]
            );
            assert!(folded.added_facts().is_empty());
            assert!(Arc::ptr_eq(&unfolded.state, &retained_unfolded.state));

            let mut missing = resource.clone();
            let ResourceClause::Declared { name, .. } = &mut missing else {
                panic!("the marker resource should be declared");
            };
            *name = "missing_marker".to_string();
            assert!(
                unfolded
                    .apply_step(SimpleProofStep::FoldResource(missing))
                    .is_err()
            );
            assert_eq!(
                unfolded.certificate().steps(),
                &[SimpleProofStep::UnfoldResource(resource.clone())]
            );
        }
    }

    #[test]
    fn execution_open_scope_owns_entry_body_and_close_transactionally() {
        let click_file = crate::lang::click::parse(
            r#"
                resource marker(x: int32) {
                    fact x == x;
                }
                verifying "two_steps.c";
                int32 two_steps(int32 x) {
                    owns marker(x);
                    immutable;
                    ensures returns_x: result == x;
                } by {
                    open(marker(x)) { step(); }
                    step();
                    frame();
                }
            "#,
        )
        .expect("test resource scope should parse");
        let function_block = &click_file.function_blocks()[0];
        let resource = function_block
            .requires()
            .iter()
            .find_map(|requirement| match requirement.inner() {
                Requirement::Resource(resource) => Some(resource.clone()),
                _ => None,
            })
            .expect("the test function should own its marker resource");
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let parsed_function =
            syntax::parse_function("int32 two_steps(int32 x) { x = x; return x; }")
                .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let empty_state = CState::new();
        let lowered = lower_resource_clause(
            &resource,
            parsed_function.parameters(),
            &arguments,
            empty_state.memory(),
        )
        .expect("the owned marker resource should lower");
        let state =
            empty_state.with_resource_context(ResourceContext::new().unchecked_with_fact(lowered));
        let reflexive = ClickProposition::Comparison {
            left: ContractExpression::CBinding("x".to_string()),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CBinding("x".to_string()),
        };
        let exposed_reflexive = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
        };

        for size in [16_u32, 64, 256, 1024, 4096] {
            let root = Proof::for_execution_frontier(
                "persistent open scope",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay: TacticReplayState {
                        source_layout: SourceExecutionLayout::new(parsed_function.body()),
                        ..TacticReplayState::default()
                    },
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let scope = root
                .begin_open(resource.clone(), 0)
                .expect("the held marker should open");
            let rejected = scope
                .begin_have(reflexive.clone())
                .expect("the open scope should begin a rejected proposition subproof");
            assert!(rejected.apply_step(SimpleProofStep::Step).is_err());
            assert!(rejected.body().certificate().steps().is_empty());
            let nested = scope
                .begin_have(reflexive.clone())
                .expect("the open scope should begin a proposition subproof")
                .apply_step(SimpleProofStep::Assumption)
                .expect("the exposed marker fact should close the nested proof");
            let scope = scope
                .join_nested(nested)
                .expect("the checked have should advance the open scope");
            let scope = scope
                .try_smart_step()
                .expect("the open body's bounded smart-step query should run")
                .expect("the owned resource scope should retain its checked statement step");
            let closed = scope.join().expect("the marker body should close");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 160 * logarithmic_height + 512;
            assert!(
                allocations <= allocation_bound,
                "size {size} open scope allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(
                closed.certificate().steps(),
                &[SimpleProofStep::Open {
                    resource: resource.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![
                        SimpleProofStep::Have {
                            proposition: reflexive.clone(),
                            proof: Box::new(ProofCertificate::from_steps(vec![
                                SimpleProofStep::Assumption,
                            ])),
                        },
                        SimpleProofStep::StepUsing(vec![exposed_reflexive.clone()]),
                    ])),
                }]
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            let sibling_scope = root
                .begin_open(resource.clone(), 0)
                .expect("the retained root should open a sibling scope");
            let sibling_nested = sibling_scope
                .begin_have(reflexive.clone())
                .expect("the sibling should begin its own nested proof")
                .apply_step(SimpleProofStep::Assumption)
                .expect("the sibling nested proof should close");
            let unrelated_scope = root
                .begin_open(resource.clone(), 0)
                .expect("the retained root should open an unrelated scope");
            assert!(unrelated_scope.join_nested(sibling_nested).is_err());
            assert!(unrelated_scope.body().certificate().steps().is_empty());
            assert!(
                closed
                    .execution()
                    .is_some_and(|execution| !execution.replay.is_at_function_exit())
            );

            let mut missing = resource.clone();
            let ResourceClause::Declared { name, .. } = &mut missing else {
                panic!("the marker resource should be declared");
            };
            *name = "missing_marker".to_string();
            assert!(root.begin_open(missing, 0).is_err());
            assert!(root.certificate().steps().is_empty());

            let terminal = root
                .begin_open(resource.clone(), 0)
                .expect("the retained root should open an alternate scope")
                .apply_step(SimpleProofStep::Step)
                .expect("the terminal scope should cross its assignment")
                .apply_step(SimpleProofStep::Step)
                .expect("the terminal scope should cross its return")
                .join()
                .expect("an exit-reaching open should defer its close");
            let terminal_execution = terminal
                .execution()
                .expect("the terminal open retains execution state");
            assert!(terminal_execution.replay.is_at_function_exit());
            assert_eq!(terminal_execution.replay.post_execution_tactics.len(), 1);
            assert_eq!(
                terminal.certificate().steps(),
                &[SimpleProofStep::Open {
                    resource: resource.clone(),
                    proof: Box::new(ProofCertificate::from_steps(vec![
                        SimpleProofStep::Step,
                        SimpleProofStep::Step,
                    ])),
                }]
            );
        }
    }

    #[test]
    fn execution_transport_forks_without_copying_unrelated_state() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 identity(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let state = CState::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(7))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(7))),
        };
        let kernel = lower_point_proposition_with_assumptions(
            &surface,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("constant equality should lower at the execution point");

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(kernel.clone());
            let mut replay = TacticReplayState::default();
            replay
                .surface_propositions
                .record_lowering(&surface, &kernel)
                .expect("the source spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "persistent transport",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let step = SimpleProofStep::TransportUsing {
                source: surface.clone(),
                target: surface.clone(),
                premises: vec![surface.clone()],
            };
            let successor = root
                .apply_step(step.clone())
                .expect("an exact identity transport should succeed");

            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert_eq!(root.certificate().steps(), &[]);
            assert_eq!(successor.certificate().steps(), &[step]);
            assert!(successor.added_facts().is_empty());
            let root_execution = root.execution().expect("root execution state");
            let successor_execution = successor.execution().expect("successor execution state");
            assert!(
                root_execution
                    .state
                    .shares_storage_with(&successor_execution.state),
                "transport does not alter the C state"
            );
            assert!(
                root_execution
                    .replay
                    .proof_certificate_builder
                    .shares_storage_with(&successor_execution.replay.proof_certificate_builder),
                "transport does not copy unrelated certificate history"
            );
            assert!(
                root_execution
                    .replay
                    .effect_facts
                    .shares_storage_with(&successor_execution.replay.effect_facts),
                "transport does not copy unrelated effect history"
            );
            assert_eq!(
                root_execution.replay.surface_propositions,
                successor_execution.replay.surface_propositions,
                "an identity transport does not change the recorded surface lowerings"
            );
        }
    }

    #[test]
    fn execution_transport_search_returns_checked_successors_and_scales() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 choose_second(int32 first, int32 second) {
                    ensures returns_second: result == second by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 choose_second(int32 first, int32 second) { first = second; return first; }",
        )
        .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let state = CState::new();
        let arguments = vec![CExpression::Value(int32(3)), CExpression::Value(int32(5))];
        let term = |variable| {
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(variable)),
            )))
        };
        let source = ClickProposition::Comparison {
            left: term(8_170_000),
            operator: ComparisonOperator::LessThan,
            right: term(8_170_001),
        };
        let missing = ClickProposition::Comparison {
            left: term(8_170_002),
            operator: ComparisonOperator::Equal,
            right: term(8_170_003),
        };
        let kernel_source = lower_point_proposition_with_assumptions(
            &source,
            &PureFactContext::new(),
            parsed_function.parameters(),
            &arguments,
            &state,
            &state,
            None,
            &ProgramPointStates::new(),
            &predicate_environment,
            &click_function_environment,
        )
        .expect("the exact transport source should lower");

        let mut samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            pure_facts.push(kernel_source.clone());
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay
                .surface_propositions
                .record_lowering(&source, &kernel_source)
                .expect("the selected source spelling should be recorded");
            let root = Proof::for_execution_frontier(
                "persistent transport search",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let progressed = root
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the meaningful assignment should advance the execution Proof");
            if size == 16 {
                let retained = progressed.clone();
                let rejected = progressed
                    .try_execution_fact_transport(&source, &missing)
                    .expect("a bounded rejected transport search should remain prompt");
                assert!(
                    rejected.is_none(),
                    "an unrelated target must not be manufactured by transport search"
                );
                assert!(Arc::ptr_eq(&progressed.state, &retained.state));
                assert!(matches!(
                    progressed.certificate().steps(),
                    [SimpleProofStep::StepUsing(_)]
                ));
            }

            let before = fact_node_allocations();
            let transported = progressed
                .try_execution_fact_transport(&source, &source)
                .expect("the bounded source candidate search should run")
                .expect("the source candidate should produce one checked transport descendant");
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                transported.certificate().steps(),
                [
                    SimpleProofStep::StepUsing(_),
                    SimpleProofStep::TransportUsing {
                        source: retained_source,
                        target,
                        premises,
                    },
                ] if retained_source == &source
                    && target == &source
                    && premises == std::slice::from_ref(&source)
            ));
            assert!(root.certificate().steps().is_empty());
        }
        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} execution transport search allocated {allocations} persistent nodes (bound {bound})"
            );
        }
    }

    #[test]
    fn smart_local_assignment_selection_ignores_unrelated_proof_facts() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 set_one(int32 x) {
                    ensures returns_one: result == 1 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 set_one(int32 x) { x = 1; return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let mut samples = Vec::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());

        for size in [16_u32, 64, 256, 1024, 4096] {
            let replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            let root = Proof::for_execution_frontier(
                "indexed local assignment",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let selected = root
                .try_indexed_statement_step()
                .expect("indexed assignment selection should remain available")
                .expect("unrelated facts should not force mutable planning");
            let allocations = fact_node_allocations() - before;
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                allocations,
            ));

            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert!(matches!(
                selected.certificate().steps(),
                [SimpleProofStep::StepUsing(premises)] if premises.is_empty()
            ));
            assert_eq!(selected.facts().to_vec(), root.facts().to_vec());
            assert!(
                !selected
                    .execution()
                    .expect("assignment successor retains execution")
                    .replay
                    .is_at_function_exit()
            );
        }

        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let logarithmic_bound = base_allocations + 8 * (height - base_height);
            assert!(
                allocations <= logarithmic_bound,
                "size {size} assignment selection allocated {allocations} persistent nodes (bound {logarithmic_bound})"
            );
        }
    }

    #[test]
    fn smart_store_selection_uses_only_statement_name_indexes() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 write_in_bounds(int32 p[], int32 i, int32 n) {
                    requires n >= 0;
                    requires n <= 2147483647;
                    requires i >= 0;
                    requires i < n;
                    requires loadable(p[0..n]);
                    consumes p[0..n];
                    mutable p[0..n] by { execute(); frame(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let parsed_function = syntax::parse_function(
            "int32 write_in_bounds(int32 p[], int32 i, int32 n) { p[i] = 9; return 0; }",
        )
        .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let (state, arguments, base_facts, base_surfaces) = initial_claim_context(
            function_block,
            &parsed_function,
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
            "indexed store selection",
        )
        .expect("the resource-backed claim context should initialize");
        let mut samples = Vec::new();

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut pure_facts = base_facts.clone();
            let mut surface_propositions = base_surfaces.clone();
            for index in 0..size {
                let fact = indexed_fact(index + 10_000);
                let surface = ClickProposition::Comparison {
                    left: ContractExpression::CFragment(CExpression::Variable(format!(
                        "unrelated_{index}"
                    ))),
                    operator: ComparisonOperator::Equal,
                    right: ContractExpression::CFragment(CExpression::Value(int32(0))),
                };
                surface_propositions
                    .record_lowering(&surface, &fact)
                    .expect("the unrelated surface fact should be indexed");
                pure_facts.push(fact);
            }
            let replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                surface_propositions,
                ..TacticReplayState::default()
            };
            let root = Proof::for_execution_frontier(
                "indexed store selection",
                0,
                ProofReplayContext {
                    state: state.clone(),
                    pure_facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let selected = root
                .try_indexed_execute_step()
                .expect("indexed store selection should remain available")
                .expect("the statement-local bounds and resource should prove the store");
            let allocations = fact_node_allocations() - before;
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                allocations,
            ));

            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            let certificate = selected.certificate();
            let [SimpleProofStep::StepUsing(premises)] = certificate.steps() else {
                panic!(
                    "the selected store should retain one explicit statement step: {:#?}",
                    certificate.steps()
                );
            };
            assert!(
                premises
                    .iter()
                    .all(|premise| !format!("{premise:?}").contains("unrelated_")),
                "the store selected an unrelated indexed fact: {premises:#?}"
            );
        }

        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let logarithmic_bound = base_allocations + 24 * (height - base_height);
            assert!(
                allocations <= logarithmic_bound,
                "size {size} indexed store selection allocated {allocations} persistent nodes (bound {logarithmic_bound})"
            );
        }
    }

    #[test]
    fn checked_statement_step_ignores_unrelated_proof_facts() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 constant(int32 x) {
                    ensures returns_one: result == 1 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 constant(int32 x) { return 1; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let unavailable = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(int32(1))),
        };
        let mut samples = Vec::new();

        for size in [16_u32, 64, 256, 1024, 4096] {
            let replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            let root = Proof::for_execution_frontier(
                "persistent statement step",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let retained_root = root.clone();
            let before_selection = fact_node_allocations();
            assert!(
                root.try_indexed_statement_step()
                    .expect("bounded smart-step selection should remain available")
                    .is_none(),
                "unrelated ambient facts require the richer transport planner"
            );
            let selection_allocations = fact_node_allocations() - before_selection;
            assert_eq!(
                selection_allocations, 0,
                "size {size} rejected terminal selection allocated persistent fact nodes"
            );
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            let marked = root
                .apply_step(SimpleProofStep::Mark("candidate".to_string()))
                .expect("a fresh proof mark should produce a checked descendant");
            assert!(matches!(
                marked.certificate().steps(),
                [SimpleProofStep::Mark(name)] if name == "candidate"
            ));
            let duplicate = marked
                .apply_step(SimpleProofStep::Mark("candidate".to_string()))
                .err()
                .expect("a duplicate mark must reject the candidate");
            assert!(duplicate.message().contains("duplicate proof mark"));
            assert!(matches!(
                marked.certificate().steps(),
                [SimpleProofStep::Mark(name)] if name == "candidate"
            ));
            let error = root
                .apply_step(SimpleProofStep::StepUsing(vec![unavailable.clone()]))
                .err()
                .expect("an unavailable explicit premise must reject the candidate");
            assert!(error.message().contains("requires an exact premise"));
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());

            let before = fact_node_allocations();
            let completed = root
                .apply_step(SimpleProofStep::Step)
                .expect("an explicit return step should certify");
            let allocations = fact_node_allocations() - before;
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                allocations,
            ));
            assert!(
                completed
                    .execution()
                    .expect("statement successor retains execution")
                    .replay
                    .is_at_function_exit()
            );
            assert!(matches!(
                completed.certificate().steps(),
                [SimpleProofStep::Step]
            ));
            let alternative = root
                .apply_step(SimpleProofStep::Step)
                .expect("the retained ancestor should support another checked descendant");
            assert_eq!(alternative.certificate(), completed.certificate());
            let root_execution = root.execution().expect("root execution state");
            let completed_execution = completed
                .execution()
                .expect("statement successor retains execution state");
            assert!(
                root_execution
                    .state
                    .shares_nonlocal_storage_with(&completed_execution.state),
                "a return step should not copy unchanged memory, resources, or populations"
            );
            let retained_completed = completed.clone();
            let exported = completed
                .into_execution_context()
                .expect("a shared checked successor should export at the legacy boundary");
            assert!(exported.replay.is_at_function_exit());
            assert!(matches!(
                retained_completed.certificate().steps(),
                [SimpleProofStep::Step]
            ));
        }

        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let logarithmic_bound = base_allocations + 24 * (height - base_height);
            assert!(
                allocations <= logarithmic_bound,
                "size {size} statement step allocated {allocations} persistent nodes (logarithmic bound {logarithmic_bound})"
            );
        }
    }

    #[test]
    fn close_invariants_is_a_transactional_constant_local_proof_step() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 loop_region(int32 x) {
                    ensures unchanged: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function("int32 loop_region(int32 x) { return x; }")
            .expect("test C function should parse");
        let function = parsed_function.to_kernel_function();
        let function_environment = CExecutionEnvironment::new();
        let arguments = vec![CExpression::Value(int32(7))];
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());

        for size in [16_u32, 64, 256, 1024, 4096] {
            let make_root = |loop_invariant_region| {
                let replay = TacticReplayState {
                    loop_invariant_region,
                    ..TacticReplayState::default()
                };
                Proof::for_execution_frontier(
                    "persistent close invariants",
                    0,
                    ProofReplayContext {
                        state: CState::new(),
                        pure_facts: (0..size).map(indexed_fact).collect(),
                        replay,
                        branch_path: PersistentSequence::default(),
                    },
                    function_block,
                    &function,
                    &parsed_function,
                    &arguments,
                    &function_environment,
                    &resource_environment,
                    &predicate_environment,
                    &click_function_environment,
                    &theorem_environment,
                )
            };

            let outside_loop = make_root(false);
            assert!(
                outside_loop
                    .apply_step(SimpleProofStep::CloseInvariants)
                    .is_err(),
                "the step is restricted to loop-region proofs"
            );
            assert!(outside_loop.certificate().steps().is_empty());

            let root = make_root(true);
            let retained_root = root.clone();
            let before = fact_node_allocations();
            let closed = root
                .apply_step(SimpleProofStep::CloseInvariants)
                .expect("the first close should produce a checked descendant");
            // The one permitted node rewrites the sole goal's execution
            // snapshot in the persistent goal collection; the bound stays
            // independent of ambient fact count.
            assert!(fact_node_allocations() - before <= 1);
            assert!(Arc::ptr_eq(&root.state, &retained_root.state));
            assert!(root.certificate().steps().is_empty());
            assert_eq!(
                closed.certificate().steps(),
                &[SimpleProofStep::CloseInvariants]
            );
            let execution = closed
                .execution()
                .expect("the successor retains execution state");
            assert!(execution.replay.region_invariants_closed);
            assert!(
                execution.replay.invariant_closer_step.is_none(),
                "source timing metadata is attached only at the replay adapter boundary"
            );
            assert!(closed.apply_step(SimpleProofStep::CloseInvariants).is_err());
            assert_eq!(
                closed.certificate().steps(),
                &[SimpleProofStep::CloseInvariants]
            );
        }
    }

    #[test]
    fn proof_condition_split_filters_conflicts_without_rebuilding_facts() {
        let symbolic = Variable(50_000);
        let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(symbolic)));
        let condition = CExpression::LessThan(
            Box::new(CExpression::Variable("x".to_string())),
            Box::new(CExpression::Value(int32(0))),
        );
        let empty = ProofFacts::default();
        let unconstrained = certified_proof_condition_transitions(
            &state,
            &empty,
            &condition,
            "persistent condition split",
        )
        .expect("a symbolic comparison should expose both paths");
        assert_eq!(unconstrained.len(), 2);
        let rejected_path_fact = unconstrained[0]
            .path_facts
            .first()
            .expect("a symbolic branch path should carry its condition fact")
            .clone();
        let selecting_fact = opposite_atomic_fact(&rejected_path_fact);

        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut available = (0..size).map(indexed_fact).collect::<Vec<_>>();
            available.push(selecting_fact.clone());
            let facts = ProofFacts::from_ordered(&available);
            assert!(facts.directly_conflicts_with(&rejected_path_fact));
            let before = fact_node_allocations();
            let transitions = certified_proof_condition_transitions(
                &state,
                &facts,
                &condition,
                "persistent condition split",
            )
            .expect("the selected condition path should certify");
            let allocations = fact_node_allocations() - before;
            let logarithmic_height = (u32::BITS - size.leading_zeros()) as usize;
            let allocation_bound = 24 * logarithmic_height + 64;
            assert!(
                allocations <= allocation_bound,
                "size {size} condition split allocated {allocations} persistent nodes (bound {allocation_bound})"
            );
            assert_eq!(transitions.len(), 1);
            assert_ne!(transitions[0].is_true, unconstrained[0].is_true);
            assert!(transitions[0].pure_facts.contains(&selecting_fact));
            assert!(matches!(
                implication_body(transitions[0].theorem.proposition()),
                Proposition::CConditionEvaluates { .. }
            ));
            assert_eq!(facts.to_vec().len(), size as usize + 1);
        }
    }

    #[test]
    fn empty_execution_branch_joins_checked_proof_arms_at_the_shared_frontier() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 identity(int32 x) {
                    ensures returns_x: result == x by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function =
            syntax::parse_function("int32 identity(int32 x) { if (x < 0) {} else {} return x; }")
                .expect("test C branch should parse");
        let function = parsed_function.to_kernel_function();
        let argument =
            CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(60_000))));
        let arguments = vec![argument];
        let function_environment = CExecutionEnvironment::new();
        let mut allocation_samples = Vec::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let mut statement_delta: Option<Vec<Proposition>> = None;
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            let root = Proof::for_execution_frontier(
                "empty branch proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let before = fact_node_allocations();
            let branches = root
                .begin_execution_branch()
                .expect("symbolic condition should open two checked arms");
            assert!(branches.arm(true).is_some());
            assert!(branches.arm(false).is_some());
            let joined = branches
                .join_empty()
                .expect("identical empty arms should rejoin");
            let allocations = fact_node_allocations() - before;
            allocation_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                allocations,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: None,
                    then_proof,
                    else_proof,
                }] if then_proof.steps().is_empty() && else_proof.steps().is_empty()
            ));
            assert!(root.certificate().steps().is_empty());
            let execution = joined
                .execution()
                .expect("joined proof should own its continuation");
            assert!(execution.replay.completed_branch_regions.contains(&0));
            assert_eq!(execution.branch_path.len(), 0);
            let completed = joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the joined continuation should execute its return");
            assert!(
                completed
                    .added_facts()
                    .iter()
                    .all(|fact| { !(0..size).any(|index| *fact == indexed_fact(index)) })
            );
            if let Some(expected) = &statement_delta {
                assert_eq!(completed.added_facts(), expected.as_slice());
            } else {
                statement_delta = Some(completed.added_facts().to_vec());
            }
            assert!(
                completed
                    .execution()
                    .expect("completed proof retains execution state")
                    .replay
                    .is_at_function_exit()
            );
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        assert!(base_allocations <= 160);
        for (size, height, allocations) in allocation_samples {
            let allocation_bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} checked execution branch allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
            );
        }
    }

    #[test]
    fn nonempty_execution_branch_retains_checked_arm_steps_at_the_join() {
        let click_file = crate::lang::click::parse(
            r#"
                theorem int32_reflexive(value: int32) {
                    ensures value == value by { normalize(); }
                }

                int32 constant(int32 x) {
                    immutable;
                    ensures returns_one: result == 1 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 constant(int32 x) { if (x < 0) { x = 1; } else { x = 1; } return x; }",
        )
        .expect("test C branch should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(70_000)),
        ))];
        let application = TheoremApplication {
            name: "int32_reflexive".to_string(),
            arguments: vec![ContractExpression::CFragment(arguments[0].clone())],
        };
        let reflexive = ClickProposition::Comparison {
            left: application.arguments[0].clone(),
            operator: ComparisonOperator::Equal,
            right: application.arguments[0].clone(),
        };
        let missing_application = TheoremApplication {
            name: "missing".to_string(),
            arguments: application.arguments.clone(),
        };
        let function_environment = CExecutionEnvironment::new();
        let mut allocation_samples = Vec::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                proof_site: Some(ProofSite::FunctionClaim {
                    function_name: "constant".to_string(),
                    claim: CProofClaim::Grouped,
                }),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            let root = Proof::for_execution_frontier(
                "nonempty branch proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let branches = root
                .begin_execution_branch()
                .expect("symbolic condition should open two checked arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("then assignment should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("else assignment should check");
            let overshoot_step = SimpleProofStep::StepUsing(Vec::new());
            let Err(overshoot) = branches.ensure_source_arm_step(true, &overshoot_step) else {
                panic!("an arm must not consume the shared return continuation");
            };
            assert!(
                overshoot
                    .message()
                    .contains("arm of `branch` must stop at the shared continuation"),
                "{overshoot:?}"
            );
            let before = fact_node_allocations();
            let joined = branches
                .join()
                .expect("identical checked assignment arms should rejoin");
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: None,
                    then_proof,
                    else_proof,
                }] if matches!(then_proof.steps(), [SimpleProofStep::StepUsing(_)])
                    && matches!(else_proof.steps(), [SimpleProofStep::StepUsing(_)])
            ));
            if size == 16 {
                assert!(
                    joined
                        .try_theorem_application(&missing_application)
                        .expect("missing theorem search should remain a bounded miss")
                        .is_none(),
                    "a missing theorem must not manufacture a descendant"
                );
                assert!(matches!(
                    joined.certificate().steps(),
                    [SimpleProofStep::Branch { .. }]
                ));
            }
            let applied = joined
                .try_theorem_application(&application)
                .expect("common theorem search should run")
                .expect("the reflexive theorem should produce a checked descendant");
            assert!(matches!(
                applied.certificate().steps(),
                [
                    SimpleProofStep::Branch { .. },
                    SimpleProofStep::ApplyTheoremUsing {
                        application: retained,
                        premises,
                    },
                ] if retained == &application && premises.is_empty()
            ));
            let scope = applied
                .begin_have(reflexive.clone())
                .expect("the joined proof should open a common nested proposition");
            // The nested proposition goal borrows the frontier's execution
            // snapshot by identity: its path-local lowering context is
            // shared, never cloned, and can never republish a frontier.
            assert!(Arc::ptr_eq(
                scope
                    .body
                    .goal_execution()
                    .expect("the nested goal borrows its lowering context"),
                applied
                    .goal_execution()
                    .expect("the joined frontier owns its snapshot"),
            ));
            let refined = scope
                .apply_step(SimpleProofStep::Assumption)
                .expect("the theorem conclusion should close the nested proposition")
                .join()
                .expect("the completed nested proposition should rejoin its root Proof");
            assert!(matches!(
                refined.certificate().steps(),
                [
                    SimpleProofStep::Branch { .. },
                    SimpleProofStep::ApplyTheoremUsing { .. },
                    SimpleProofStep::Have {
                        proposition,
                        proof,
                    },
                ] if proposition == &reflexive
                    && proof.steps() == [SimpleProofStep::Assumption]
            ));
            let completed = refined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the joined continuation should execute its return");
            assert!(
                completed
                    .execution()
                    .expect("completed proof retains execution state")
                    .replay
                    .is_at_function_exit()
            );
            let framed = completed
                .try_smart_frame_at(None, 2, 2)
                .expect("common terminal frame search should run")
                .expect("the immutable effect should produce a checked descendant");
            allocation_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                framed.certificate().steps(),
                [
                    SimpleProofStep::Branch { .. },
                    SimpleProofStep::ApplyTheoremUsing { .. },
                    SimpleProofStep::Have { .. },
                    SimpleProofStep::StepUsing(_),
                    SimpleProofStep::FrameUsing {
                        region: None,
                        premises,
                    },
                ] if premises.is_empty()
            ));
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        for (size, height, allocations) in allocation_samples {
            let allocation_bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} branch, theorem, have, common return, and frame allocated {allocations} persistent nodes (logarithmic bound {allocation_bound})"
            );
        }
    }

    #[test]
    fn branch_interface_is_checked_per_arm_and_scales_with_its_delta() {
        let click_file = crate::lang::click::parse(
            r#"
                abstract resource marker();
                abstract resource permit();

                resource ready() {
                    contains permit();
                }

                int32 nonnegative(int32 x) {
                    ensures nonnegative_result: result >= 0 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 nonnegative(int32 x) { if (x < 0) { x = 1; } else { x = 2; } return x; }",
        )
        .expect("test interface branch should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(72_000)),
        ))];
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let variable =
            |name: &str| ContractExpression::CFragment(CExpression::Variable(name.to_string()));
        let value = |constant| ContractExpression::CFragment(CExpression::Value(int32(constant)));
        let nonnegative = ClickProposition::Comparison {
            left: variable("x"),
            operator: ComparisonOperator::GreaterEqual,
            right: value(0),
        };
        let negative = ClickProposition::Comparison {
            left: variable("x"),
            operator: ComparisonOperator::LessThan,
            right: value(0),
        };
        let make_root = |size: u32, state: CState| {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            Proof::for_execution_frontier(
                "branch interface proof",
                0,
                ProofReplayContext {
                    state,
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            )
        };

        let mut samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let root = make_root(size, CState::new());
            let branches = root
                .begin_execution_branch()
                .expect("symbolic condition should open both interface arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("then assignment should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("else assignment should check");
            let before = fact_node_allocations();
            let joined = branches
                .join_with_interface(vec![ProofAssertion::Fact(nonnegative.clone())])
                .expect("both assignments should establish the interface");
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: Some(assertions),
                    then_proof,
                    else_proof,
                }] if assertions == std::slice::from_ref(&ProofAssertion::Fact(nonnegative.clone()))
                    && matches!(then_proof.steps(), [SimpleProofStep::StepUsing(_)])
                    && matches!(else_proof.steps(), [SimpleProofStep::StepUsing(_)])
            ));
            assert!(
                joined
                    .added_facts()
                    .iter()
                    .all(|fact| !(0..size).any(|index| *fact == indexed_fact(index))),
                "the interface node must not copy ambient facts into its delta"
            );
            let completed = joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the abstract joined frontier should execute its return");
            assert!(
                completed
                    .execution()
                    .expect("completed interface proof retains execution")
                    .replay
                    .is_at_function_exit()
            );
        }
        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let bound = base_allocations + 48 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} branch interface allocated {allocations} persistent nodes (bound {bound})"
            );
        }

        let root = make_root(16, CState::new());
        let retained = root.clone();
        let error = root
            .begin_execution_branch()
            .expect("rejection test should open both arms")
            .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
            .expect("then assignment should check")
            .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
            .expect("else assignment should check")
            .join_with_interface(vec![ProofAssertion::Fact(negative)])
            .err()
            .expect("each arm must independently establish the interface");
        assert!(error.message().contains("did not establish fact"));
        assert!(Arc::ptr_eq(&root.state, &retained.state));
        assert!(root.certificate().steps().is_empty());

        // An arm advanced under a different split of the same root has
        // identical replay metadata — both splits opened the same C `if` —
        // so only the recorded entry marker distinguishes it. The join must
        // reject the splice transactionally.
        let root = make_root(16, CState::new());
        let genuine = root
            .begin_execution_branch()
            .expect("identity test should open both arms")
            .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
            .expect("then assignment should check")
            .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
            .expect("else assignment should check");
        let foreign = root
            .begin_execution_branch()
            .expect("a second split of the same root should open both arms")
            .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
            .expect("foreign then assignment should check");
        let mut spliced = genuine.clone();
        spliced.arms[0] = foreign.arms[0].clone();
        let error = spliced
            .join_with_interface(Vec::new())
            .err()
            .expect("a foreign arm must not satisfy this split's join");
        assert!(
            error.message().contains("did not derive from split"),
            "{error:?}"
        );
        assert!(root.certificate().steps().is_empty());
        genuine
            .join_with_interface(Vec::new())
            .expect("the recorded arms still join after the rejected splice");

        let marker_clause = ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Token,
            name: "marker".to_string(),
            arguments: Vec::new(),
            parameter_types: Vec::new(),
        };
        let marker_fact = CResourceFact::own_token("marker".to_string(), Vec::new());
        let mut ownership_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let resources = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
                }))
                .unchecked_with_fact(marker_fact.clone());
            let branches = make_root(16, CState::new().with_resource_context(resources))
                .begin_execution_branch()
                .expect("the owned-interface condition should expose both arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("owned-interface then assignment should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("owned-interface else assignment should check");
            let assertions = vec![ProofAssertion::Resource(marker_clause.clone())];
            let before = fact_node_allocations();
            let joined = branches
                .join_with_interface(assertions.clone())
                .expect("an exact unchanged owned resource should rejoin");
            ownership_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: Some(retained),
                    ..
                }] if retained == assertions.as_slice()
            ));
            joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the exact owned interface should retain its return frontier");
        }
        let (_, base_height, base_allocations) = ownership_samples[0];
        for (size, height, allocations) in ownership_samples {
            let bound = base_allocations + 64 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} exact owned interface allocated {allocations} persistent nodes (bound {bound})"
            );
        }

        let ready_clause = ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Composite,
            name: "ready".to_string(),
            arguments: Vec::new(),
            parameter_types: Vec::new(),
        };
        let permit_fact = CResourceFact::own_token("permit".to_string(), Vec::new());
        let mut changed_snapshot_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let resources = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
                }))
                .unchecked_with_fact(permit_fact.clone());
            let branches = make_root(16, CState::new().with_resource_context(resources))
                .begin_execution_branch()
                .expect("the transformed-interface condition should expose both arms");
            assert!(
                branches.supports_interface_branch(),
                "a structural preflight must not require a resource folded later in the arms"
            );
            let branches = branches
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("transformed-interface then assignment should check")
                .apply_step(true, SimpleProofStep::FoldResource(ready_clause.clone()))
                .expect("then arm should fold its ready resource")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("transformed-interface else assignment should check")
                .apply_step(false, SimpleProofStep::FoldResource(ready_clause.clone()))
                .expect("else arm should independently fold its ready resource");
            let then_resources = branches
                .arm(true)
                .expect("then arm should remain feasible")
                .execution()
                .expect("then arm should retain execution")
                .state
                .resources();
            let else_resources = branches
                .arm(false)
                .expect("else arm should remain feasible")
                .execution()
                .expect("else arm should retain execution")
                .state
                .resources();
            assert!(!then_resources.shares_storage_with(else_resources));

            let assertions = vec![ProofAssertion::Resource(ready_clause.clone())];
            let before = fact_node_allocations();
            let joined = branches
                .join_with_interface(assertions)
                .expect("independently folded resource snapshots should rejoin");
            changed_snapshot_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    then_proof,
                    else_proof,
                    ..
                }] if matches!(
                    then_proof.steps(),
                    [SimpleProofStep::StepUsing(_), SimpleProofStep::FoldResource(_)]
                ) && matches!(
                    else_proof.steps(),
                    [SimpleProofStep::StepUsing(_), SimpleProofStep::FoldResource(_)]
                )
            ));
            joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("the transformed owned interface should retain its return frontier");
        }
        let (_, base_height, base_allocations) = changed_snapshot_samples[0];
        for (size, height, allocations) in changed_snapshot_samples {
            let bound = base_allocations + 96 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} changed-resource Proof join allocated {allocations} persistent nodes (bound {bound})"
            );
        }

        let represented_quantity = CResourceFact::own_quantity(
            CResource::Token {
                name: "marker".to_string(),
                arguments: Vec::new(),
            },
            Bitvector32Term::Constant(2),
        );
        let mut normalized_quantity_samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let resources = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_token(format!("quantity_unrelated_{index}"), Vec::new())
                }))
                .unchecked_with_fact(represented_quantity.clone());
            let branches = make_root(16, CState::new().with_resource_context(resources))
                .begin_execution_branch()
                .expect("the normalized-ownership probe should expose both arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("normalized-ownership then assignment should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("normalized-ownership else assignment should check");
            let before = fact_node_allocations();
            let normalized_join = branches
                .join_with_interface(vec![ProofAssertion::Resource(marker_clause.clone())])
                .expect("an entailed quantity representation should be consumed and restored once");
            normalized_quantity_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(
                normalized_join
                    .execution()
                    .expect("normalized interface retains execution")
                    .state
                    .resources()
                    .contains_exact_representation(&represented_quantity),
                "the common quantity must not be duplicated or weakened by its unit interface"
            );
        }
        let (_, base_height, base_allocations) = normalized_quantity_samples[0];
        for (size, height, allocations) in normalized_quantity_samples {
            let bound = base_allocations + 160 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} normalized quantity interface allocated {allocations} persistent nodes (bound {bound})"
            );
        }

        let invalid_branches = make_root(
            16,
            CState::new().with_resource_context(
                ResourceContext::new().unchecked_with_fact(represented_quantity),
            ),
        )
        .begin_execution_branch()
        .expect("the rejected quantity probe should expose both arms")
        .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
        .expect("rejected quantity then assignment should check")
        .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
        .expect("rejected quantity else assignment should check");
        let invalid_root = invalid_branches.root.clone();
        let quantity_three = ResourceClause::Quantified {
            quantity: ContractExpression::CFragment(CExpression::Value(int32(3))),
            resource: Box::new(marker_clause),
        };
        assert!(
            invalid_branches
                .join_with_interface(vec![ProofAssertion::Resource(quantity_three)])
                .is_err(),
            "an interface may not manufacture a quantity larger than either arm owns"
        );
        assert!(invalid_root.certificate().steps().is_empty());
    }

    #[test]
    fn nested_end_of_arm_interface_derives_its_enclosing_continuation() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 nested(int32 x, int32 flag) {
                    ensures nonnegative_result: result >= 0 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 nested(int32 x, int32 flag) { if (flag != 0) { if (x < 0) { x = 1; } else { x = 2; } } else { x = 3; } return x; }",
        )
        .expect("test nested interface branch should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![
            CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(73_000)))),
            CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(73_001)))),
        ];
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let nonnegative = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
            operator: ComparisonOperator::GreaterEqual,
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        };
        let make_root = |size: u32| {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            Proof::for_execution_frontier(
                "nested branch interface proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            )
        };

        let mut samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let outer = make_root(size)
                .begin_execution_branch()
                .expect("outer symbolic condition should expose both arms");
            let outer_statement = outer.statement_index;
            let outer_then = outer
                .arm(true)
                .expect("outer then arm should be feasible")
                .clone();
            let nested = outer_then
                .begin_execution_branch()
                .expect("nested symbolic condition should expose both arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("nested then assignment should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("nested else assignment should check");
            let nested_statement = nested.statement_index;
            assert!(nested.continuation_remaining.is_none());

            let before = fact_node_allocations();
            let joined = nested
                .join_with_interface(vec![ProofAssertion::Fact(nonnegative.clone())])
                .expect("nested end-of-arm interface should reach the outer continuation");
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            let execution = joined
                .execution()
                .expect("nested join should retain execution");
            assert!(
                execution
                    .replay
                    .completed_branch_regions
                    .contains(&nested_statement)
            );
            assert!(
                execution
                    .replay
                    .completed_branch_regions
                    .contains(&outer_statement)
            );
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::Branch {
                    ensuring: Some(assertions),
                    ..
                }] if assertions == std::slice::from_ref(&ProofAssertion::Fact(nonnegative.clone()))
            ));
            let completed = joined
                .apply_step(SimpleProofStep::StepUsing(Vec::new()))
                .expect("derived enclosing continuation should execute the return");
            assert!(
                completed
                    .execution()
                    .expect("completed nested proof retains execution")
                    .replay
                    .is_at_function_exit()
            );
        }
        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let bound = base_allocations + 64 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} nested branch interface allocated {allocations} persistent nodes (bound {bound})"
            );
        }
    }

    #[test]
    fn decided_execution_branch_retains_one_checked_path_without_copying_context() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 selected(int32 x) {
                    ensures returns_one: result == 1 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 selected(int32 x) { if (x < 0) { x = 1; } else { x = 2; } return x; }",
        )
        .expect("test decided C branch should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(75_000)),
        ))];
        let function_environment = CExecutionEnvironment::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let make_root = |facts: Vec<Proposition>| {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            Proof::for_execution_frontier(
                "decided branch proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: facts,
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            )
        };

        let probe = make_root(Vec::new())
            .begin_execution_branch()
            .expect("the unconstrained condition should expose both arms");
        let selecting_fact = probe.arms[0]
            .as_ref()
            .expect("the then arm should be feasible")
            .introduced_facts
            .iter()
            .next()
            .expect("the then arm should retain its condition fact")
            .clone();
        let rejecting_fact = probe.arms[1]
            .as_ref()
            .expect("the else arm should be feasible")
            .introduced_facts
            .iter()
            .next()
            .expect("the else arm should retain its condition fact")
            .clone();
        let mut samples = Vec::new();
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = (0..size).map(indexed_fact).collect::<Vec<_>>();
            facts.push(selecting_fact.clone());
            let root = make_root(facts);
            let branches = root
                .begin_execution_branch()
                .expect("the selecting fact should make exactly one arm feasible");
            assert_eq!(branches.sole_feasible_arm(), Some(true));
            assert!(branches.arm(false).is_none());
            let branches = branches
                .try_smart_step(true)
                .expect("smart selection should remain bounded")
                .expect("the assignment should produce a checked simple successor");
            let before = fact_node_allocations();
            let decided = branches
                .finish_decided()
                .expect("the sole checked arm should form a decided path");
            samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                decided.certificate().steps(),
                [SimpleProofStep::If {
                    then_proof,
                    else_proof,
                    ..
                }] if matches!(
                    then_proof.steps(),
                    [SimpleProofStep::StepUsing(decision), SimpleProofStep::StepUsing(_)]
                        if !decision.is_empty()
                ) && else_proof.steps().is_empty()
            ));
            assert_eq!(
                decided
                    .execution()
                    .expect("decided path retains execution")
                    .branch_path
                    .len(),
                0
            );
            assert!(
                decided
                    .added_facts()
                    .iter()
                    .all(|fact| !(0..size).any(|index| *fact == indexed_fact(index))),
                "the decided node delta must not copy unrelated ambient facts"
            );
            let completed = decided
                .try_indexed_execute_step()
                .expect("contextual return selection should remain bounded")
                .expect("the continuation return should check with retained branch facts");
            assert!(
                completed
                    .execution()
                    .expect("completed decided proof retains execution")
                    .replay
                    .is_at_function_exit()
            );
        }
        let (_, base_height, base_allocations) = samples[0];
        for (size, height, allocations) in samples {
            let bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= bound,
                "size {size} decided branch allocated {allocations} persistent nodes (logarithmic bound {bound})"
            );
        }

        let branches = make_root(vec![rejecting_fact])
            .begin_execution_branch()
            .expect("the rejecting fact should retain only the else arm");
        assert_eq!(branches.sole_feasible_arm(), Some(false));
        let branches = branches
            .try_smart_step(false)
            .expect("else-arm smart selection should remain bounded")
            .expect("the else assignment should produce a checked successor");
        let decided = branches
            .finish_decided()
            .expect("the sole else arm should form a decided path");
        let certificate = decided.certificate();
        assert!(
            matches!(
            certificate.steps(),
            [SimpleProofStep::If {
                condition,
                then_proof,
                else_proof,
            }] if then_proof.steps().is_empty()
                && matches!(
                    else_proof.steps(),
                    [SimpleProofStep::StepUsing(decision), SimpleProofStep::StepUsing(_)]
                        if matches!(decision.as_slice(), [fact]
                            if *fact == negate_click_proposition(condition))
                )
            ),
            "{certificate:#?}"
        );
    }

    #[test]
    fn terminal_execution_branch_retains_distinct_outcomes_as_a_logical_if() {
        let click_file = crate::lang::click::parse(
            r#"
                int32 choose(int32 x) {
                    ensures returns_one_or_two: result == 1 or result == 2 by { assumption(); }
                }
            "#,
        )
        .expect("test function contract should parse");
        let function_block = &click_file.function_blocks()[0];
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment =
            ClickFunctionEnvironment::new(click_file.click_function_definitions());
        let theorem_environment = TheoremEnvironment::new(click_file.theorem_definitions());
        let parsed_function = syntax::parse_function(
            "int32 choose(int32 x) { if (x < 0) { return 1; } else { return 2; } }",
        )
        .expect("test terminal C branch should parse");
        let function = parsed_function.to_kernel_function();
        let arguments = vec![CExpression::Value(CValue::Int32(
            Bitvector32Term::Variable(Variable(80_000)),
        ))];
        let function_environment = CExecutionEnvironment::new();
        let mut allocation_samples = Vec::new();
        let resource_environment = ResourceEnvironment::new(click_file.resource_definitions());
        let mut expected_outcome_fact_sizes = None;
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut replay = TacticReplayState {
                source_layout: SourceExecutionLayout::new(parsed_function.body()),
                ..TacticReplayState::default()
            };
            replay.frontier.next_statement_index = 0;
            let root = Proof::for_execution_frontier(
                "terminal branch proof",
                0,
                ProofReplayContext {
                    state: CState::new(),
                    pure_facts: (0..size).map(indexed_fact).collect(),
                    replay,
                    branch_path: PersistentSequence::default(),
                },
                function_block,
                &function,
                &parsed_function,
                &arguments,
                &function_environment,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let branches = root
                .begin_execution_branch()
                .expect("symbolic condition should open two checked arms")
                .apply_step(true, SimpleProofStep::StepUsing(Vec::new()))
                .expect("then return should check")
                .apply_step(false, SimpleProofStep::StepUsing(Vec::new()))
                .expect("else return should check");
            assert!(branches.both_arms_at_function_exit());
            let before = fact_node_allocations();
            let joined = branches
                .join_terminal()
                .expect("two checked returns should form a terminal logical case split");
            allocation_samples.push((
                size,
                (u32::BITS - size.leading_zeros()) as usize,
                fact_node_allocations() - before,
            ));
            assert!(matches!(
                joined.certificate().steps(),
                [SimpleProofStep::If {
                    condition,
                    then_proof,
                    else_proof,
                }] if matches!(
                    then_proof.steps(),
                    [SimpleProofStep::StepUsing(entry), SimpleProofStep::StepUsing(body)]
                        if entry == std::slice::from_ref(condition) && body.is_empty()
                ) && matches!(
                    else_proof.steps(),
                    [SimpleProofStep::StepUsing(entry), SimpleProofStep::StepUsing(body)]
                        if matches!(entry.as_slice(), [fact]
                            if *fact == negate_click_proposition(condition))
                            && body.is_empty()
                )
            ));
            assert!(root.certificate().steps().is_empty());
            let execution = joined
                .execution()
                .expect("terminal join should retain execution state");
            assert!(execution.replay.is_at_function_exit());
            let outcome_paths = execution
                .replay
                .execution()
                .expect("terminal join should retain outcomes")
                .paths();
            assert_eq!(outcome_paths.len(), 2);
            let outcome_fact_sizes = outcome_paths
                .iter()
                .map(|path| path.execution_facts().len())
                .collect::<Vec<_>>();
            if let Some(expected) = &expected_outcome_fact_sizes {
                assert_eq!(
                    &outcome_fact_sizes, expected,
                    "terminal outcome paths must not copy the growing ambient fact context"
                );
            } else {
                expected_outcome_fact_sizes = Some(outcome_fact_sizes);
            }
            assert_eq!(execution.branch_path.len(), 0);
        }
        let (_, base_height, base_allocations) = allocation_samples[0];
        for (size, height, allocations) in allocation_samples {
            let allocation_bound = base_allocations + 32 * (height - base_height);
            assert!(
                allocations <= allocation_bound,
                "size {size} terminal branch join allocated {allocations} persistent fact nodes (logarithmic bound {allocation_bound})"
            );
        }
    }
}
