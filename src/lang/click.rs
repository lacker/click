//! Tiny `.click` sidecar verifier for the C0 kernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::instrumentation::{self, TacticEvent, VerificationEvent};
use crate::kernel::{
    Bitvector32Term, BitvectorEqualityDerivationStep, CCheckedFunctionExecution,
    CComparisonOperator, CCompositeResourceDefinition, CConditionOutcome, CExecutionEnvironment,
    CExecutionSemantics, CExpression, CExpressionOutcome, CFunction, CFunctionContractClaim,
    CFunctionContractClaimKey, CFunctionContractClaimTarget, CFunctionContractExecutionMode,
    CFunctionExecutionCandidates, CFunctionOutcome, CFunctionSpecification, CLoopEffect,
    CLoopEffectCheck, CLoopEffectSpan, CLoopInvariantCheck, CMemory, CMemoryRange, CMemorySegment,
    CResource, CResourceAccessMode, CResourceFact, CResourceSpec, CState, CStatement,
    CStatementOutcome, CType, CValue, CVerifiedLoopRule, CVerifiedPureTheorem, ConditionTerm,
    ExecutionBudget, ExecutionPureFact, Pointer, PointerBlock, PointerOffsetTerm, ProofObligation,
    Proposition, PropositionDerivation, PureFactContext, ResourceContext,
    ResourceContextValidityError, Sort, SpecExpression, SpecMemory, SpecPredicateArgument,
    SpecProposition, SpecResource, SymbolicCExecution, Term, Theorem, Variable,
    abstract_c_state_for_join, c_condition_fact_has_memory, c_condition_fact_memories,
    c_expression_definedness_proposition, c_function, c_function_contract_entry_state,
    c_function_entry_state, c_function_execution_candidates_from_outcomes,
    c_function_outcome_from_statement_outcome,
    c_function_outcomes_program_state_definitionally_equal,
    c_function_outcomes_program_state_equal_by_execution_provenance, c_function_specification,
    c_function_termination_plan, c_if, c_loop_effects_hold_at_back_edge,
    c_loop_invariant_obligations_at_entry, c_loop_invariants_hold_at_back_edge_using,
    c_loop_invariants_hold_at_entry, c_loop_preservation_contexts,
    c_pointer_offsets_proven_equal_for_effect, c_pointer_value, c_resources_directly_match, c_seq,
    c_unverified_function_contract_claims, c_verified_function_contract_claims,
    c_verified_function_rule, c_verified_function_termination_rules,
    c_while_with_invariant_and_effect_checks,
    certify_c_function_execution_path_resource_representation,
    certify_int32_above_one_predecessor_is_at_least_one,
    certify_int32_move_one_from_right_to_left_preserves_sum,
    checked_c_function_execution_with_entry_derivations, int32,
    prove_c_condition_fact_direct_transport, prove_c_condition_fact_transport,
    prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems,
    prove_c_function_satisfies_specification_from_symbolic_path,
    prove_checked_c_function_execution_with_environment, prove_forall_int32_application,
    prove_int32_above_one_predecessor_is_at_least_one,
    prove_int32_add_nonnegative_left_is_at_least_right,
    prove_int32_add_nonnegative_right_is_at_least_left, prove_int32_ge_and_not_gt_implies_eq,
    prove_int32_ge_implies_reversed_le, prove_int32_ge_transitive,
    prove_int32_increment_below_max_is_defined, prove_int32_increment_greater_equal_lower_bound,
    prove_int32_increment_lower_bound, prove_int32_increment_preserves_order,
    prove_int32_increment_strict_greater_lower_bound, prove_int32_increment_strictly_increases,
    prove_int32_increment_upper_bound, prove_int32_le_and_neq_implies_lt,
    prove_int32_le_and_not_lt_implies_eq, prove_int32_le_antisymmetric,
    prove_int32_le_implies_reversed_ge, prove_int32_le_lt_transitive, prove_int32_le_transitive,
    prove_int32_lt_implies_le, prove_int32_lt_le_transitive, prove_int32_lt_transitive,
    prove_int32_move_one_from_right_to_left_preserves_sum,
    prove_int32_nonnegative_add_within_max_is_defined,
    prove_int32_nonnegative_predecessor_upper_bound,
    prove_int32_nonnegative_subtract_within_value_is_defined, prove_int32_not_lt_implies_ge,
    prove_int32_one_plus_below_max_is_defined, prove_int32_one_plus_strictly_increases,
    prove_int32_positive_is_nonnegative, prove_int32_positive_predecessor_is_nonnegative,
    prove_int32_positive_predecessor_strictly_decreases,
    prove_int32_strictly_positive_is_nonnegative, prove_int32_successor_le_implies_lt,
    prove_owned_resource_count_lower_bound, prove_owned_resource_quantity_nonnegative,
    prove_symbolic_c_condition_evaluation,
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget,
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget,
    prove_universally_quantified_pure_implication,
    prove_universally_quantified_pure_implication_by_int32_rewrites,
    substitute_int32_variable_in_proposition,
};
use crate::lang::c::syntax::{self, C0Expression, C0Type};
use crate::persistent::{PersistentMap, PersistentSet};

mod checking;
mod diagnostics;
mod expansion;
mod lowering;
mod parser;
mod printing;
mod proof;
mod validation;
mod verification;

use checking::*;
pub use expansion::{
    CProofClaim, SmartTacticSourceSite, SourcePosition, c0_smart_tactic_source_sites,
    c0_tactic_source_position, expand_c0_claim_source, expand_c0_claim_source_by_label,
    expand_c0_tactic_source_at, verifying_source_paths,
};
use expansion::{ExpansionCapture, ProofSite, VerificationTarget, verification_target_at};
use lowering::*;
use parser::ContractLetBinding;
pub use printing::{format_proof_certificate, format_proof_tactics};
use proof::*;
use validation::{
    combined_click_function_definitions, combined_predicate_definitions,
    combined_resource_definitions, combined_theorem_definitions,
    combined_theorem_definitions_with_stdlib_ensure_count, contains_at_expression,
    contains_old_expression, describe_c0_type, describe_resource_clause,
    proposition_contains_at_expression, proposition_contains_old_expression,
    proposition_contains_resource_count,
};
pub(in crate::lang::click) use verification::*;
pub use verification::{
    C0IncrementalSelection, c0_function_names, c0_incremental_selection, parse, verify_c0_sources,
    verify_c0_sources_at, verify_c0_sources_functions, verify_click_theorems,
};

const POINTER_ARGUMENT_VARIABLE_BASE: u64 = 100_000;
const COUNTED_POPULATION_VARIABLE_BASE: u64 = 200_000;
const MAX_CONCRETE_RANGE_FOLD_STEPS: i64 = 1024;
/// Maximum UTF-8 bytes in an ordinary verifier error message. Set
/// `CLICK_FULL_DIAGNOSTICS=1` when an engine investigation needs unbounded
/// internal state.
pub const DEFAULT_DIAGNOSTIC_BYTE_LIMIT: usize = 16 * 1024;
pub const FULL_DIAGNOSTICS_ENV: &str = "CLICK_FULL_DIAGNOSTICS";

/// User-visible word spellings recognized by Surface Click, including
/// contextual syntax words and compatibility-only spellings. Documentation
/// coverage compares this registry bidirectionally with its public inventory.
pub const SURFACE_CLICK_WORDS: &[&str] = &[
    "abstract",
    "all",
    "and",
    "any",
    "apply",
    "apply_loop_summary",
    "as",
    "assumption",
    "at",
    "auto",
    "bounded_execute",
    "branch",
    "by",
    "byte_offset",
    "c",
    "calculate",
    "cases",
    "choose",
    "close_invariants",
    "conjunction",
    "consumes",
    "contains",
    "contradiction",
    "count",
    "counted",
    "decreases",
    "defined",
    "double_negation",
    "else",
    "ensures",
    "ensuring",
    "entry",
    "enumerate",
    "execute",
    "execute_else_step",
    "execute_rest",
    "execute_step",
    "execute_then_step",
    "execute_until",
    "exists",
    "exit",
    "extract",
    "fact",
    "fold",
    "forall",
    "frame",
    "from",
    "function",
    "have",
    "if",
    "immutable",
    "implies",
    "induct",
    "initialize",
    "instantiate",
    "int32",
    "intro",
    "invariant",
    "left",
    "let",
    "load_int32",
    "load_int32_pointer",
    "load_uint8",
    "load_uint8_pointer",
    "loadable",
    "loop",
    "mark",
    "memory",
    "mutable",
    "normalize",
    "not",
    "object",
    "observe",
    "of",
    "old",
    "open",
    "or",
    "owns",
    "predicate",
    "preserve",
    "produces",
    "read",
    "requirement",
    "requires",
    "resource",
    "rewrite",
    "right",
    "separate",
    "simp",
    "sizeof",
    "split",
    "statement",
    "step",
    "struct",
    "summarize",
    "symbolic_execute",
    "theorem",
    "then",
    "transport",
    "uint8",
    "unfold",
    "using",
    "vacuous",
    "verifying",
    "views",
    "void",
    "where",
    "witness",
    "write",
];

/// Stable identifiers for the documented Surface Click declaration,
/// contract, proposition, expression, and operator families. Individual word
/// forms are tracked separately in [`SURFACE_CLICK_WORDS`].
pub const SURFACE_CLICK_FORMS: &[&str] = &[
    "all",
    "and",
    "any",
    "at",
    "at-expression",
    "auto",
    "by",
    "c-fragment",
    "contains",
    "contains-proposition",
    "decreases",
    "defined",
    "effect",
    "ensures",
    "exists",
    "fold",
    "forall",
    "function",
    "if-expression",
    "immutable",
    "implies",
    "let-where",
    "loadable",
    "modifies",
    "mutable",
    "not",
    "old",
    "operator-bit-and",
    "operator-bit-not",
    "operator-bit-or",
    "operator-bit-xor",
    "operator-divide",
    "operator-eq",
    "operator-field",
    "operator-ge",
    "operator-gt",
    "operator-index",
    "operator-le",
    "operator-lt",
    "operator-minus",
    "operator-multiply",
    "operator-ne",
    "operator-plus",
    "operator-range",
    "operator-remainder",
    "operator-shift-left",
    "operator-shift-right",
    "or",
    "predicate",
    "predicate-call",
    "preserves",
    "read",
    "requires",
    "resource",
    "resource-clause",
    "separate",
    "theorem",
    "verifying",
    "write",
];

const CLICK_STANDARD_LIBRARY: &str = include_str!("../../stdlib/prelude.click");

/// Emits one non-overlapping verifier phase on every exit path, including an
/// early `?`. Profiling enables this with `CLICK_TIMINGS`; ordinary
/// verification pays only one environment lookup and an `Instant` read.
struct VerificationTimingPhase {
    name: &'static str,
    started: std::time::Instant,
    enabled: bool,
}

impl VerificationTimingPhase {
    fn new(name: &'static str) -> Self {
        let enabled = instrumentation::enabled();
        if enabled {
            instrumentation::emit(VerificationEvent::PhaseStarted(name));
        }
        Self {
            name,
            started: std::time::Instant::now(),
            enabled,
        }
    }
}

impl Drop for VerificationTimingPhase {
    fn drop(&mut self) {
        if self.enabled {
            instrumentation::emit(VerificationEvent::PhaseFinished {
                name: self.name,
                elapsed: self.started.elapsed(),
            });
        }
    }
}

fn check_verification_deadline() -> Result<(), ClickError> {
    if instrumentation::deadline_exceeded() {
        Err(ClickError::new(format!(
            "verification budget exhausted inside {}",
            instrumentation::deadline_context()
        )))
    } else {
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFile {
    verifying_sources: Vec<String>,
    predicate_definitions: Vec<PredicateDefinition>,
    click_function_definitions: Vec<ClickFunctionDefinition>,
    resource_definitions: Vec<ResourceDefinition>,
    theorem_definitions: Vec<TheoremDefinition>,
    function_blocks: Vec<FunctionBlock>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PredicateDefinition {
    name: String,
    parameters: Vec<FunctionParameter>,
    body: ClickProposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickFunctionDefinition {
    name: String,
    parameters: Vec<FunctionParameter>,
    return_type: C0Type,
    decreases: Option<ContractExpression>,
    body: ContractExpression,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceDefinition {
    name: String,
    parameters: Vec<FunctionParameter>,
    composite_body: Option<CompositeResourceBody>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompositeResourceBody {
    condition: Option<ClickProposition>,
    contains: Vec<ResourceClause>,
    facts: Vec<ClickProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TheoremDefinition {
    name: String,
    parameters: Vec<FunctionParameter>,
    requires: Vec<Requirement>,
    ensures: Vec<EnsureClause>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClickFunctionType {
    parameters: Vec<FunctionParameter>,
    return_type: C0Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionBlock {
    signature: FunctionSignature,
    requires: Vec<Requirement>,
    /// Parsed once so a simple `choose(... from requirement label)` step does
    /// not linearly rescan every function requirement.
    requirement_label_indices: BTreeMap<String, usize>,
    decreases: Option<CFunctionDecrease>,
    structural_clauses: Vec<StructuralClause>,
    effects: Vec<EffectClause>,
    ensures: Vec<EnsureClause>,
    grouped_proof: Option<SourceProof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CFunctionDecrease {
    Numeric(ContractExpression),
    Resource(ResourceClause),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSignature {
    return_type: C0Type,
    name: String,
    parameters: Vec<FunctionParameter>,
    /// Byte spans declared by sized array parameter spellings
    /// (`int32 p[2]`), used to certify requirement side-obligations.
    declared_loadable_bytes: Vec<(String, u32)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionParameter {
    c_type: C0Type,
    name: String,
    struct_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    Labeled {
        label: String,
        requirement: Box<Requirement>,
    },
    LoadableSegment {
        segment: ContractSegment,
    },
    Resource(ResourceClause),
    Proposition(ClickProposition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnsureClause {
    name: Option<String>,
    ensure: Ensure,
    proof: SourceProof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectClause {
    effect: Effect,
    proof: SourceProof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralClause {
    region: CodeRegion,
    label: Option<String>,
    decreases: Option<ContractExpression>,
    items: Vec<StructuralItem>,
    initialize_proof: Option<SourceProof>,
    preserve_proof: Option<SourceProof>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum CodeRegion {
    Function,
    Loop(usize),
    Statement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralItem {
    kind: StructuralItemKind,
    claim: StructuralItemClaim,
    proof: SourceProof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StructuralItemClaim {
    Proposition(ClickProposition),
    Effect(Effect),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralItemKind {
    Invariant,
    Effect,
    StepEffect,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ensure {
    Proposition(ClickProposition),
    Resource(ResourceClause),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceClause {
    ViewMemory(ContractSegment),
    OwnMemory(ContractSegment),
    Quantified {
        quantity: ContractExpression,
        resource: Box<ResourceClause>,
    },
    Declared {
        access: ResourceAccessMode,
        kind: ResourceKind,
        name: String,
        arguments: Vec<ContractExpression>,
        parameter_types: Vec<C0Type>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceSubject {
    Memory(ContractSegment),
    Declared {
        kind: ResourceKind,
        name: String,
        arguments: Vec<ContractExpression>,
        parameter_types: Vec<C0Type>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceAccessMode {
    Own,
    View,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceKind {
    Composite,
    Token,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Effect {
    Immutable,
    Mutable(Vec<ContractSegment>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ClickProposition {
    Comparison {
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
    },
    Separate {
        left: ResourceSubject,
        right: ResourceSubject,
    },
    Contains {
        parent: ResourceSubject,
        child: ResourceSubject,
    },
    Loadable {
        segment: ContractSegment,
    },
    Defined {
        expression: ContractExpression,
    },
    At {
        selector: SnapshotSelector,
        proposition: Box<ClickProposition>,
    },
    And(Box<ClickProposition>, Box<ClickProposition>),
    Or(Box<ClickProposition>, Box<ClickProposition>),
    Not(Box<ClickProposition>),
    Implies(Box<ClickProposition>, Box<ClickProposition>),
    ForAll {
        c_type: C0Type,
        name: String,
        body: Box<ClickProposition>,
    },
    Exists {
        c_type: C0Type,
        name: String,
        body: Box<ClickProposition>,
    },
    RangeAll {
        start: ContractExpression,
        end: ContractExpression,
        item: String,
        body: Box<ClickProposition>,
    },
    RangeAny {
        start: ContractExpression,
        end: ContractExpression,
        item: String,
        body: Box<ClickProposition>,
    },
    PredicateCall {
        name: String,
        arguments: Vec<ContractExpression>,
    },
}

/// surface forms paired with the exact kernel propositions they lowered
/// to in one proof context.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SurfacePropositionMap {
    storage: std::sync::Arc<SurfacePropositionStorage>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct SurfacePropositionStorage {
    by_kernel: PersistentMap<Proposition, KernelSurfaceForms>,
    /// Recorded kernel facts grouped by a structural key that forgets only
    /// memory snapshot identities. Typed proof steps use this to recover a
    /// check-equivalent surface form without scanning ambient facts.
    by_snapshot_blind:
        PersistentMap<proof::SnapshotBlindPropositionKey, PersistentSet<Proposition>>,
    // The debug form is a deterministic structural bucket key. Exact
    // equality inside the bucket preserves soundness even if two future
    // syntax variants ever acquire the same debug rendering.
    by_surface: PersistentMap<String, Vec<(ClickProposition, KernelLowerings)>>,
    /// Kernel facts with a current surface form that reads one named C
    /// local. Assignment-step search probes only the assigned local's bucket
    /// instead of scanning every recorded fact.
    by_current_c_variable: PersistentMap<String, PersistentSet<Proposition>>,
    /// Kernel facts whose recorded surface form is one top-level
    /// predicate call. Checked predicate unfolds use this narrow bucket to
    /// recover an already-materialized body without scanning ambient facts.
    by_predicate: PersistentMap<String, PersistentSet<Proposition>>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct KernelSurfaceForms {
    ordered: Vec<ClickProposition>,
    by_debug_key: BTreeMap<String, Vec<ClickProposition>>,
}

impl KernelSurfaceForms {
    fn insert(&mut self, surface: &ClickProposition, debug_key: &str) {
        let bucket = self.by_debug_key.entry(debug_key.to_string()).or_default();
        if bucket.contains(surface) {
            return;
        }
        bucket.push(surface.clone());
        self.ordered.push(surface.clone());
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct KernelLowerings {
    ordered: Vec<Proposition>,
    exact: BTreeSet<Proposition>,
}

impl KernelLowerings {
    fn insert(&mut self, kernel: &Proposition) {
        if self.exact.insert(kernel.clone()) {
            self.ordered.push(kernel.clone());
        }
    }
}

fn collect_c_expression_variables(expression: &CExpression, names: &mut BTreeSet<String>) {
    match expression {
        CExpression::Value(_) => {}
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::AddressOf(inner)
        | CExpression::PointerOffsetBytes { pointer: inner, .. }
        | CExpression::Not(inner)
        | CExpression::BitwiseNot(inner)
        | CExpression::Load(inner)
        | CExpression::TypedLoad { pointer: inner, .. } => {
            collect_c_expression_variables(inner, names);
        }
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
            collect_c_expression_variables(left, names);
            collect_c_expression_variables(right, names);
        }
    }
}

fn collect_current_segment_variables(segment: &ContractSegment, names: &mut BTreeSet<String>) {
    if segment.state != ContractSegmentState::Current {
        return;
    }
    collect_c_expression_variables(&segment.base, names);
    collect_c_expression_variables(&segment.start, names);
    collect_c_expression_variables(&segment.end, names);
}

fn collect_current_resource_clause_variables(
    resource: &ResourceClause,
    names: &mut BTreeSet<String>,
) {
    match resource {
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            collect_current_segment_variables(segment, names);
        }
        ResourceClause::Quantified { quantity, resource } => {
            collect_current_contract_expression_variables(quantity, names);
            collect_current_resource_clause_variables(resource, names);
        }
        ResourceClause::Declared { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
    }
}

fn collect_current_resource_subject_variables(
    subject: &ResourceSubject,
    names: &mut BTreeSet<String>,
) {
    match subject {
        ResourceSubject::Memory(segment) => collect_current_segment_variables(segment, names),
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
    }
}

fn collect_current_contract_expression_variables(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::CFragment(expression) => {
            collect_c_expression_variables(expression, names);
        }
        ContractExpression::Field { base, lowered, .. } => {
            collect_current_contract_expression_variables(base, names);
            collect_c_expression_variables(lowered, names);
        }
        ContractExpression::CBinding(_) | ContractExpression::ResourceWildcard => {}
        ContractExpression::ResourceCount(resource) => {
            collect_current_resource_clause_variables(resource, names);
        }
        // Explicitly anchored expressions are stable across a local write.
        ContractExpression::Old(_) | ContractExpression::At { .. } => {}
        ContractExpression::BitwiseNot(inner) => {
            collect_current_contract_expression_variables(inner, names);
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            collect_current_contract_expression_variables(left, names);
            collect_current_contract_expression_variables(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_current_proposition_variables(condition, names);
            collect_current_contract_expression_variables(then_branch, names);
            collect_current_contract_expression_variables(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_current_contract_expression_variables(start, names);
            collect_current_contract_expression_variables(end, names);
            collect_current_contract_expression_variables(initial, names);
            collect_current_contract_expression_variables(body, names);
        }
        ContractExpression::Let { value, body, .. } => {
            collect_current_contract_expression_variables(value, names);
            collect_current_contract_expression_variables(body, names);
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
    }
}

fn collect_current_proposition_variables(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_current_contract_expression_variables(left, names);
            collect_current_contract_expression_variables(right, names);
        }
        ClickProposition::Separate { left, right }
        | ClickProposition::Contains {
            parent: left,
            child: right,
        } => {
            collect_current_resource_subject_variables(left, names);
            collect_current_resource_subject_variables(right, names);
        }
        ClickProposition::Loadable { segment } => {
            collect_current_segment_variables(segment, names);
        }
        ClickProposition::Defined { expression } => {
            collect_current_contract_expression_variables(expression, names);
        }
        // The proposition itself is anchored, so current-local writes cannot
        // change its meaning even if its body contains a C fragment.
        ClickProposition::At { .. } => {}
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_current_proposition_variables(left, names);
            collect_current_proposition_variables(right, names);
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            collect_current_proposition_variables(body, names);
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_current_contract_expression_variables(start, names);
            collect_current_contract_expression_variables(end, names);
            collect_current_proposition_variables(body, names);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_current_contract_expression_variables(argument, names);
            }
        }
    }
}

impl SurfacePropositionMap {
    #[cfg(test)]
    pub(crate) fn shares_persistent_storage_with(&self, other: &Self) -> bool {
        self.storage
            .by_kernel
            .shares_root_with(&other.storage.by_kernel)
            && self
                .storage
                .by_surface
                .shares_root_with(&other.storage.by_surface)
            && self
                .storage
                .by_snapshot_blind
                .shares_root_with(&other.storage.by_snapshot_blind)
            && self
                .storage
                .by_current_c_variable
                .shares_root_with(&other.storage.by_current_c_variable)
            && self
                .storage
                .by_predicate
                .shares_root_with(&other.storage.by_predicate)
    }

    pub fn record_lowering(
        &mut self,
        surface: &ClickProposition,
        kernel: &Proposition,
    ) -> Result<(), ClickError> {
        let mut current_c_variables = BTreeSet::new();
        collect_current_proposition_variables(surface, &mut current_c_variables);
        let surface_key = format!("{surface:?}");
        {
            let storage = std::sync::Arc::make_mut(&mut self.storage);
            if let ClickProposition::PredicateCall { name, .. } = surface {
                let existing = storage.by_predicate.get(name);
                if !existing.is_some_and(|facts| facts.contains(kernel)) {
                    let facts = existing
                        .cloned()
                        .unwrap_or_default()
                        .with_value(kernel.clone());
                    storage.by_predicate = storage.by_predicate.with_inserted(name.clone(), facts);
                }
            }
            for name in current_c_variables {
                let existing = storage.by_current_c_variable.get(&name);
                if existing.is_some_and(|facts| facts.contains(kernel)) {
                    continue;
                }
                let facts = existing
                    .cloned()
                    .unwrap_or_default()
                    .with_value(kernel.clone());
                storage.by_current_c_variable =
                    storage.by_current_c_variable.with_inserted(name, facts);
            }
            let mut forms = storage.by_kernel.get(kernel).cloned().unwrap_or_default();
            forms.insert(surface, &surface_key);
            storage.by_kernel = storage.by_kernel.with_inserted(kernel.clone(), forms);
            let snapshot_key = proof::snapshot_blind_proposition_key(kernel);
            let snapshot_facts = storage
                .by_snapshot_blind
                .get(&snapshot_key)
                .cloned()
                .unwrap_or_default()
                .with_value(kernel.clone());
            storage.by_snapshot_blind = storage
                .by_snapshot_blind
                .with_inserted(snapshot_key, snapshot_facts);
            let mut bucket = storage
                .by_surface
                .get(&surface_key)
                .cloned()
                .unwrap_or_default();
            let lowerings = if let Some((_, lowerings)) =
                bucket.iter_mut().find(|(recorded, _)| recorded == surface)
            {
                lowerings
            } else {
                bucket.push((surface.clone(), KernelLowerings::default()));
                &mut bucket
                    .last_mut()
                    .expect("surface lowering was just inserted")
                    .1
            };
            lowerings.insert(kernel);
            storage.by_surface = storage.by_surface.with_inserted(surface_key, bucket);
        }
        match (surface, kernel) {
            (ClickProposition::And(surface_left, surface_right), Proposition::And(left, right))
            | (ClickProposition::Or(surface_left, surface_right), Proposition::Or(left, right))
            | (
                ClickProposition::Implies(surface_left, surface_right),
                Proposition::Implies(left, right),
            ) => {
                self.record_lowering(surface_left, left)?;
                self.record_lowering(surface_right, right)
            }
            // Click comparison negation is lowered by flipping the comparison
            // polarity, so either kernel boolean is possible (for example,
            // `not (x != 0)` becomes equality with polarity `true`).
            (ClickProposition::Not(_), Proposition::ConditionIs(_, _)) => Ok(()),
            (ClickProposition::Not(surface_body), Proposition::Not(body)) => {
                self.record_lowering(surface_body, body)
            }
            (
                ClickProposition::ForAll {
                    body: surface_body, ..
                },
                Proposition::ForAll { body, .. },
            )
            | (
                ClickProposition::Exists {
                    body: surface_body, ..
                },
                Proposition::Exists { body, .. },
            ) => self.record_lowering(surface_body, body),
            // A connective's kernel form may collapse when one leg resolves
            // concretely (a materialized cell decides `i <= len` at a loop
            // exit, and the simplifier keeps only the live leg). Record the
            // whole kernel against whichever leg still matches its
            // structure; a kernel matching neither leg is a real
            // mislowering and still errors below.
            (
                ClickProposition::And(surface_left, surface_right)
                | ClickProposition::Or(surface_left, surface_right)
                | ClickProposition::Implies(surface_left, surface_right),
                kernel,
            ) if self.clone().record_lowering(surface_left, kernel).is_ok()
                || self.clone().record_lowering(surface_right, kernel).is_ok() =>
            {
                if self.record_lowering(surface_left, kernel).is_err() {
                    self.record_lowering(surface_right, kernel)?;
                }
                Ok(())
            }
            (ClickProposition::And(_, _), _)
            | (ClickProposition::Or(_, _), _)
            | (ClickProposition::Not(_), _)
            | (ClickProposition::Implies(_, _), _)
            | (ClickProposition::ForAll { .. }, _)
            | (ClickProposition::Exists { .. }, _) => Err(ClickError::new(format!(
                "surface proposition did not lower to matching logical structure: {surface:?} -> {kernel:?}"
            ))),
            _ => Ok(()),
        }
    }

    pub(in crate::lang::click) fn kernels_written_by_predicate(
        &self,
        name: &String,
    ) -> impl Iterator<Item = &Proposition> {
        self.storage
            .by_predicate
            .get(name)
            .into_iter()
            .flat_map(PersistentSet::iter)
    }

    pub fn surface(&self, kernel: &Proposition) -> Result<&ClickProposition, ClickError> {
        self.storage
            .by_kernel
            .get(kernel)
            .and_then(|forms| forms.ordered.last())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "kernel proposition has no recorded Click surface form: {kernel:?}"
                ))
            })
    }

    pub fn surfaces(&self, kernel: &Proposition) -> impl Iterator<Item = &ClickProposition> {
        self.storage
            .by_kernel
            .get(kernel)
            .into_iter()
            .flat_map(|forms| forms.ordered.iter())
    }

    pub(in crate::lang::click) fn snapshot_blind_kernels(
        &self,
        kernel: &Proposition,
    ) -> impl Iterator<Item = &Proposition> {
        let key = proof::snapshot_blind_proposition_key(kernel);
        self.storage
            .by_snapshot_blind
            .get(&key)
            .into_iter()
            .flat_map(PersistentSet::iter)
    }

    pub fn kernel_facts(&self) -> impl Iterator<Item = &Proposition> {
        self.storage.by_kernel.keys()
    }

    pub(crate) fn current_c_variable_kernel_facts(
        &self,
        name: &str,
    ) -> impl Iterator<Item = &Proposition> {
        self.storage
            .by_current_c_variable
            .get(&name.to_string())
            .into_iter()
            .flat_map(PersistentSet::iter)
    }

    #[cfg(test)]
    pub(crate) fn current_c_variable_lookup_comparisons(&self, name: &str) -> usize {
        self.storage
            .by_current_c_variable
            .lookup_comparisons(&name.to_string())
    }

    pub fn available_kernel(
        &self,
        surface: &ClickProposition,
        available: &[Proposition],
    ) -> Option<&Proposition> {
        self.available_kernel_matching(surface, |kernel| available.contains(kernel))
    }

    pub(crate) fn available_kernel_matching(
        &self,
        surface: &ClickProposition,
        mut is_available: impl FnMut(&Proposition) -> bool,
    ) -> Option<&Proposition> {
        let surface_key = format!("{surface:?}");
        let mut matches = self
            .storage
            .by_surface
            .get(&surface_key)?
            .iter()
            .find_map(|(recorded, lowerings)| (recorded == surface).then_some(lowerings))?
            .ordered
            .iter()
            .filter(|kernel| {
                crate::instrumentation::record_deterministic_work(1);
                is_available(kernel)
            });
        let kernel = matches.next()?;
        matches.next().is_none().then_some(kernel)
    }

    pub fn unique_kernel(&self, surface: &ClickProposition) -> Option<&Proposition> {
        let surface_key = format!("{surface:?}");
        let mut lowerings = self
            .storage
            .by_surface
            .get(&surface_key)?
            .iter()
            .find_map(|(recorded, lowerings)| (recorded == surface).then_some(lowerings))?
            .ordered
            .iter();
        let kernel = lowerings.next()?;
        lowerings.next().is_none().then_some(kernel)
    }

    pub fn has_distinct_lowering(&self, surface: &ClickProposition, kernel: &Proposition) -> bool {
        let surface_key = format!("{surface:?}");
        self.storage
            .by_surface
            .get(&surface_key)
            .into_iter()
            .flatten()
            .find_map(|(recorded, lowerings)| (recorded == surface).then_some(lowerings))
            .is_some_and(|lowerings| lowerings.ordered.iter().any(|lowered| lowered != kernel))
    }

    pub fn checked_surface<F>(
        &self,
        kernel: &Proposition,
        mut lower_in_current_state: F,
    ) -> Result<ClickProposition, ClickError>
    where
        F: FnMut(&ClickProposition) -> Result<Proposition, ClickError>,
    {
        let forms = self.storage.by_kernel.get(kernel).ok_or_else(|| {
            ClickError::new(format!(
                "kernel proposition has no recorded Click surface form: {kernel:?}"
            ))
        })?;
        let mut last_mismatch = None;
        for surface in forms.ordered.iter().rev() {
            match lower_in_current_state(surface) {
                Ok(lowered) if &lowered == kernel => return Ok(surface.clone()),
                Ok(lowered) => last_mismatch = Some(format!("{surface:?} -> {lowered:?}")),
                Err(error) => last_mismatch = Some(format!("{surface:?} -> {}", error.message())),
            }
        }
        Err(ClickError::new(format!(
            "none of the recorded surface forms lower to the proposition at the current proof state{}; expected {kernel:?}",
            last_mismatch
                .map(|mismatch| format!(" (last mismatch: {mismatch})"))
                .unwrap_or_default()
        )))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ContractExpression {
    /// A C0 expression fragment appearing inside Surface Click.
    CFragment(CExpression),
    /// A source-level struct field place paired with its lowered C expression.
    ///
    /// The source place is retained for certificates and diagnostics; only
    /// `lowered` crosses into semantic checking.
    Field {
        base: Box<ContractExpression>,
        field: String,
        lowered: CExpression,
    },
    /// A binding from the verified C function's lexical environment.
    ///
    /// This is distinct from contract built-ins such as bare `result`, even
    /// when the C binding has the same source name.
    CBinding(String),
    /// The authoritative population count of one instantiated counted
    /// resource family. This expression is only meaningful while the
    /// family's population body is in scope.
    ResourceCount(Box<ResourceClause>),
    /// A wildcard argument inside the resource pattern accepted by
    /// `count(...)`. It is never a standalone contract expression.
    ResourceWildcard,
    Old(Box<ContractExpression>),
    At {
        selector: SnapshotSelector,
        expression: Box<ContractExpression>,
    },
    Add(Box<ContractExpression>, Box<ContractExpression>),
    Subtract(Box<ContractExpression>, Box<ContractExpression>),
    Multiply(Box<ContractExpression>, Box<ContractExpression>),
    Divide(Box<ContractExpression>, Box<ContractExpression>),
    Remainder(Box<ContractExpression>, Box<ContractExpression>),
    ShiftLeft(Box<ContractExpression>, Box<ContractExpression>),
    ShiftRight(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseAnd(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseOr(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseXor(Box<ContractExpression>, Box<ContractExpression>),
    BitwiseNot(Box<ContractExpression>),
    Index(Box<ContractExpression>, Box<ContractExpression>),
    If {
        condition: Box<ClickProposition>,
        then_branch: Box<ContractExpression>,
        else_branch: Box<ContractExpression>,
    },
    RangeFold {
        start: Box<ContractExpression>,
        end: Box<ContractExpression>,
        initial: Box<ContractExpression>,
        accumulator: String,
        item: String,
        body: Box<ContractExpression>,
    },
    Let {
        name: String,
        c_type: Option<C0Type>,
        value: Box<ContractExpression>,
        body: Box<ContractExpression>,
    },
    Call {
        name: String,
        arguments: Vec<ContractExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClickArrayRef {
    memory: CMemory,
    pointer: Pointer,
    element_type: CType,
}

type ClickArrayRefs = BTreeMap<String, ClickArrayRef>;
#[derive(Clone)]
struct RecordedSnapshots {
    version: std::sync::Arc<RecordedSnapshotVersion>,
}

struct RecordedSnapshotVersion {
    root: Option<std::sync::Arc<RecordedSnapshotNode>>,
    history: Option<std::sync::Arc<RecordedSnapshotChange>>,
    origin: std::sync::Arc<()>,
}

impl Default for RecordedSnapshots {
    fn default() -> Self {
        Self {
            version: std::sync::Arc::new(RecordedSnapshotVersion {
                root: None,
                history: None,
                origin: std::sync::Arc::new(()),
            }),
        }
    }
}

#[derive(Clone)]
struct RecordedSnapshotNode {
    selector: SnapshotSelector,
    state: Option<CState>,
    left: Option<std::sync::Arc<RecordedSnapshotNode>>,
    right: Option<std::sync::Arc<RecordedSnapshotNode>>,
    height: u8,
}

/// One persistent map mutation. Proof branches share their complete prefix;
/// an audited join can therefore visit only the keys changed in either arm
/// instead of intersecting every snapshot accumulated by the project.
#[derive(Clone)]
struct RecordedSnapshotChange {
    selector: SnapshotSelector,
    parent: Option<std::sync::Arc<RecordedSnapshotChange>>,
}

#[cfg(test)]
thread_local! {
    static RECORDED_SNAPSHOT_NODE_ALLOCATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn recorded_snapshot_node_allocations() -> usize {
    RECORDED_SNAPSHOT_NODE_ALLOCATIONS.with(std::cell::Cell::get)
}

impl RecordedSnapshots {
    fn new() -> Self {
        Self::default()
    }

    fn get<K: RecordedSnapshotKey + ?Sized>(&self, key: &K) -> Option<&CState> {
        let mut node = self.version.root.as_deref();
        while let Some(current) = node {
            match key.compare(&current.selector) {
                std::cmp::Ordering::Less => node = current.left.as_deref(),
                std::cmp::Ordering::Greater => node = current.right.as_deref(),
                std::cmp::Ordering::Equal => return current.state.as_ref(),
            }
        }
        None
    }

    fn contains_key<K: RecordedSnapshotKey + ?Sized>(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    fn insert(&mut self, selector: impl Into<SnapshotSelector>, state: CState) -> Option<CState> {
        let selector = selector.into();
        let prior = self.get(&selector).cloned();
        self.version = std::sync::Arc::new(RecordedSnapshotVersion {
            root: Some(recorded_snapshot_insert(
                self.version.root.as_ref(),
                selector.clone(),
                Some(state),
            )),
            history: Some(std::sync::Arc::new(RecordedSnapshotChange {
                selector,
                parent: self.version.history.clone(),
            })),
            origin: self.version.origin.clone(),
        });
        prior
    }

    fn remove<K: RecordedSnapshotKey + ?Sized>(&mut self, key: &K) -> Option<CState> {
        let selector = key.to_selector();
        let prior = self.get(key).cloned();
        if prior.is_some() {
            self.version = std::sync::Arc::new(RecordedSnapshotVersion {
                root: Some(recorded_snapshot_insert(
                    self.version.root.as_ref(),
                    selector.clone(),
                    None,
                )),
                history: Some(std::sync::Arc::new(RecordedSnapshotChange {
                    selector,
                    parent: self.version.history.clone(),
                })),
                origin: self.version.origin.clone(),
            });
        }
        prior
    }

    /// Intersects two descendants of one exact persistent ancestor by
    /// visiting only the keys changed after the fork.
    ///
    /// This is the recorded-snapshot merge required by a proof-level execution
    /// case split. Returning `None` for unrelated histories prevents a caller
    /// from treating structurally similar maps as branches of the same proof.
    fn common_descendant(&self, other: &Self, ancestor: &Self) -> Option<Self> {
        fn changed_keys_since(
            descendant: &RecordedSnapshots,
            ancestor: &RecordedSnapshots,
            changed: &mut BTreeSet<SnapshotSelector>,
        ) -> bool {
            let mut current = descendant.version.history.as_ref();
            loop {
                match (current, ancestor.version.history.as_ref()) {
                    (Some(left), Some(right)) if std::sync::Arc::ptr_eq(left, right) => {
                        return true;
                    }
                    (None, None) => return true,
                    (Some(change), _) => {
                        changed.insert(change.selector.clone());
                        current = change.parent.as_ref();
                    }
                    (None, Some(_)) => return false,
                }
            }
        }

        if !std::sync::Arc::ptr_eq(&self.version.origin, &ancestor.version.origin)
            || !std::sync::Arc::ptr_eq(&other.version.origin, &ancestor.version.origin)
        {
            return None;
        }
        let mut changed = BTreeSet::new();
        if !changed_keys_since(self, ancestor, &mut changed)
            || !changed_keys_since(other, ancestor, &mut changed)
        {
            return None;
        }
        let mut common = ancestor.clone();
        for selector in changed {
            match (self.get(&selector), other.get(&selector)) {
                (Some(left), Some(right)) if left == right => {
                    common.insert(selector, left.clone());
                }
                _ => {
                    common.remove(&selector);
                }
            }
        }
        Some(common)
    }

    fn iter(&self) -> std::vec::IntoIter<(&SnapshotSelector, &CState)> {
        let mut entries = Vec::new();
        recorded_snapshot_entries(self.version.root.as_deref(), &mut entries);
        entries.into_iter()
    }

    fn keys(&self) -> impl DoubleEndedIterator<Item = &SnapshotSelector> {
        self.iter().map(|(selector, _)| selector)
    }

    fn retain(&mut self, mut keep: impl FnMut(&SnapshotSelector, &mut CState) -> bool) {
        let mut retained = Self::new();
        for (selector, state) in self.iter() {
            let mut state = state.clone();
            if keep(selector, &mut state) {
                retained.insert(selector.clone(), state);
            }
        }
        *self = retained;
    }
}

trait RecordedSnapshotKey {
    fn compare(&self, selector: &SnapshotSelector) -> std::cmp::Ordering;
    fn to_selector(&self) -> SnapshotSelector;
}

impl RecordedSnapshotKey for SnapshotSelector {
    fn compare(&self, selector: &SnapshotSelector) -> std::cmp::Ordering {
        self.cmp(selector)
    }

    fn to_selector(&self) -> SnapshotSelector {
        self.clone()
    }
}

impl RecordedSnapshotKey for ProgramPointRef {
    fn compare(&self, selector: &SnapshotSelector) -> std::cmp::Ordering {
        SnapshotSelector::ProgramPoint(self.clone()).cmp(selector)
    }

    fn to_selector(&self) -> SnapshotSelector {
        SnapshotSelector::ProgramPoint(self.clone())
    }
}

impl std::fmt::Debug for RecordedSnapshots {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

impl PartialEq for RecordedSnapshots {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl Eq for RecordedSnapshots {}

fn recorded_snapshot_height(node: Option<&std::sync::Arc<RecordedSnapshotNode>>) -> u8 {
    node.map_or(0, |node| node.height)
}

fn recorded_snapshot_node(
    selector: SnapshotSelector,
    state: Option<CState>,
    left: Option<std::sync::Arc<RecordedSnapshotNode>>,
    right: Option<std::sync::Arc<RecordedSnapshotNode>>,
) -> std::sync::Arc<RecordedSnapshotNode> {
    #[cfg(test)]
    RECORDED_SNAPSHOT_NODE_ALLOCATIONS.with(|allocations| allocations.set(allocations.get() + 1));
    let height =
        1 + recorded_snapshot_height(left.as_ref()).max(recorded_snapshot_height(right.as_ref()));
    std::sync::Arc::new(RecordedSnapshotNode {
        selector,
        state,
        left,
        right,
        height,
    })
}

fn recorded_snapshot_balance(
    selector: SnapshotSelector,
    state: Option<CState>,
    mut left: Option<std::sync::Arc<RecordedSnapshotNode>>,
    mut right: Option<std::sync::Arc<RecordedSnapshotNode>>,
) -> std::sync::Arc<RecordedSnapshotNode> {
    let balance = i16::from(recorded_snapshot_height(left.as_ref()))
        - i16::from(recorded_snapshot_height(right.as_ref()));
    if balance > 1 {
        let left_root = left.as_ref().expect("left-heavy AVL node has a left child");
        if recorded_snapshot_height(left_root.left.as_ref())
            < recorded_snapshot_height(left_root.right.as_ref())
        {
            let pivot = left_root
                .right
                .as_ref()
                .expect("left-right AVL rotation has a pivot");
            left = Some(recorded_snapshot_node(
                pivot.selector.clone(),
                pivot.state.clone(),
                Some(recorded_snapshot_node(
                    left_root.selector.clone(),
                    left_root.state.clone(),
                    left_root.left.clone(),
                    pivot.left.clone(),
                )),
                pivot.right.clone(),
            ));
        }
        let pivot = left.as_ref().expect("left AVL rotation has a pivot");
        return recorded_snapshot_node(
            pivot.selector.clone(),
            pivot.state.clone(),
            pivot.left.clone(),
            Some(recorded_snapshot_node(
                selector,
                state,
                pivot.right.clone(),
                right,
            )),
        );
    }
    if balance < -1 {
        let right_root = right
            .as_ref()
            .expect("right-heavy AVL node has a right child");
        if recorded_snapshot_height(right_root.right.as_ref())
            < recorded_snapshot_height(right_root.left.as_ref())
        {
            let pivot = right_root
                .left
                .as_ref()
                .expect("right-left AVL rotation has a pivot");
            right = Some(recorded_snapshot_node(
                pivot.selector.clone(),
                pivot.state.clone(),
                pivot.left.clone(),
                Some(recorded_snapshot_node(
                    right_root.selector.clone(),
                    right_root.state.clone(),
                    pivot.right.clone(),
                    right_root.right.clone(),
                )),
            ));
        }
        let pivot = right.as_ref().expect("right AVL rotation has a pivot");
        return recorded_snapshot_node(
            pivot.selector.clone(),
            pivot.state.clone(),
            Some(recorded_snapshot_node(
                selector,
                state,
                left,
                pivot.left.clone(),
            )),
            pivot.right.clone(),
        );
    }
    recorded_snapshot_node(selector, state, left, right)
}

fn recorded_snapshot_insert(
    root: Option<&std::sync::Arc<RecordedSnapshotNode>>,
    selector: SnapshotSelector,
    state: Option<CState>,
) -> std::sync::Arc<RecordedSnapshotNode> {
    let Some(root) = root else {
        return recorded_snapshot_node(selector, state, None, None);
    };
    match selector.cmp(&root.selector) {
        std::cmp::Ordering::Less => recorded_snapshot_balance(
            root.selector.clone(),
            root.state.clone(),
            Some(recorded_snapshot_insert(
                root.left.as_ref(),
                selector,
                state,
            )),
            root.right.clone(),
        ),
        std::cmp::Ordering::Greater => recorded_snapshot_balance(
            root.selector.clone(),
            root.state.clone(),
            root.left.clone(),
            Some(recorded_snapshot_insert(
                root.right.as_ref(),
                selector,
                state,
            )),
        ),
        std::cmp::Ordering::Equal => {
            recorded_snapshot_node(selector, state, root.left.clone(), root.right.clone())
        }
    }
}

fn recorded_snapshot_entries<'a>(
    node: Option<&'a RecordedSnapshotNode>,
    entries: &mut Vec<(&'a SnapshotSelector, &'a CState)>,
) {
    let Some(node) = node else {
        return;
    };
    recorded_snapshot_entries(node.left.as_deref(), entries);
    if let Some(state) = &node.state {
        entries.push((&node.selector, state));
    }
    recorded_snapshot_entries(node.right.as_deref(), entries);
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecArrayRef {
    memory: SpecMemory,
    pointer: SpecExpression,
    element_type: CType,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpecElaborationContext {
    values: BTreeMap<String, SpecExpression>,
    array_refs: BTreeMap<String, SpecArrayRef>,
    current_memory: SpecMemory,
    current_loop_entry: Option<usize>,
    function_contract: bool,
}

impl Default for SpecElaborationContext {
    fn default() -> Self {
        Self {
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            current_memory: SpecMemory::Current,
            current_loop_entry: None,
            function_contract: false,
        }
    }
}

impl SpecElaborationContext {
    fn with_current_memory(current_memory: SpecMemory) -> Self {
        Self {
            current_memory,
            ..Self::default()
        }
    }

    fn for_loop_invariant(loop_index: usize) -> Self {
        Self {
            current_loop_entry: Some(loop_index),
            ..Self::default()
        }
    }

    fn for_function_contract() -> Self {
        Self {
            function_contract: true,
            ..Self::default()
        }
    }

    fn old_state(
        &self,
        entry_values: &BTreeMap<String, CValue>,
        entry_memory: &CMemory,
    ) -> Result<Self, String> {
        if self.function_contract {
            return Ok(Self {
                values: self.values.clone(),
                array_refs: BTreeMap::new(),
                current_memory: SpecMemory::FunctionEntry,
                current_loop_entry: None,
                function_contract: true,
            });
        }
        let mut values = entry_values
            .iter()
            .map(|(name, value)| (name.clone(), SpecExpression::Value(value.clone())))
            .collect::<BTreeMap<_, _>>();

        for (name, value) in &self.values {
            if !matches!(value, SpecExpression::Value(_)) {
                return Err(format!(
                    "`old(...)` cannot capture non-fixed spec value `{name}`: `{value:?}`"
                ));
            }
            values.insert(name.clone(), value.clone());
        }

        Ok(Self {
            values,
            array_refs: BTreeMap::new(),
            current_memory: SpecMemory::Fixed(entry_memory.clone()),
            current_loop_entry: None,
            function_contract: false,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractSegment {
    state: ContractSegmentState,
    base: CExpression,
    start: CExpression,
    end: CExpression,
    surface: ContractSegmentSurface,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ContractSegmentSurface {
    Range {
        base: ContractExpression,
        start: ContractExpression,
        end: ContractExpression,
    },
    Field(String),
    Object(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ContractSegmentState {
    Current,
    Old,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

impl fmt::Display for ComparisonOperator {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let form = match self {
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
        };
        formatter.write_str(form)
    }
}

/// A `.click` `by` clause proving one theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SourceProof {
    Default,
    Tactic(SmartTactic),
    Script(Vec<ProofTactic>),
}

#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedStatementTransition {
    pub(crate) theorem: Theorem,
    pub(crate) outcome: CStatementOutcome,
    pub(crate) execution_facts: Vec<ExecutionPureFact>,
    pub(crate) path_facts: Vec<Proposition>,
    pub(crate) obligations: Vec<ProofObligation>,
    pub(crate) pure_facts: Vec<Proposition>,
    /// Facts emitted by this statement transition itself, after applying the
    /// same snapshot transports reflected in `pure_facts`. This is an
    /// output-sized semantic delta; it deliberately excludes inherited
    /// ambient facts without rediscovering them by set difference.
    pub(crate) introduced_facts: Vec<Proposition>,
    pub(crate) prerequisite_derivations: Vec<PropositionDerivation>,
    /// Exact entry-state facts consumed while planning this
    /// transition. Kept outside the kernel theorem so collecting certificate
    /// provenance cannot perturb execution paths or fresh identities.
    pub(crate) planning_premises: Vec<Proposition>,
    pub(crate) fact_transports: Vec<CertifiedFactTransport>,
}

#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedFactTransport {
    pub(crate) source: Proposition,
    pub(crate) target: Proposition,
    pub(crate) theorem: Theorem,
    pub(crate) statement_local: bool,
    /// Exact facts the bounded frame check consumed to carry `source`
    /// across the statement effect; check frames the fact from exactly
    /// these.
    pub(crate) frame_premises: Vec<Proposition>,
}

/// Private semantic evidence retained while a smart tactic constructs its
/// [`ProofCertificate`]. This is planner metadata, not a proof step and cannot
/// cross the smart/simple boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct PlannedStatementTransition {
    pub(crate) transition: CertifiedStatementTransition,
    pub(crate) next_opaque_call: u64,
    pub(crate) next_kernel_variable: u64,
}

/// A tactic in an explicit `.click` proof script.
///
/// Tactics are classified by [`ProofTactic::class`]. A `SourceProof::Script`
/// certificate is not considered fully expanded while it contains a smart
/// tactic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofTactic {
    Mark(String),
    Step,
    SmartExecute,
    SmartExecuteAllPaths,
    ExecuteUntil(CodeRegionRef),
    SmartFrame(Option<CodeRegionRef>),
    FrameUsing {
        region: Option<CodeRegionRef>,
        premises: Vec<ClickProposition>,
    },
    UnfoldPredicate(String),
    UnfoldResource(ResourceClause),
    FoldResource(ResourceClause),
    Induct {
        parameter: String,
        hypothesis: String,
    },
    ApplyInduction {
        hypothesis: String,
        argument: ContractExpression,
    },
    CloseInduction,
    ApplyTheorem(TheoremApplication),
    ApplyTheoremUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    Have(ProofHave),
    Open(ProofOpen),
    If(ProofIf),
    Cases(ProofCases),
    Branch(ProofBranch),
    Loop(StructuralClause),
    ObserveResource(ResourceClause),
    Witness(ProofWitness),
    Choose(ProofChoice),
    Assumption,
    Extract(ClickProposition),
    Normalize,
    Intro,
    Split,
    Left,
    Right,
    Enumerate,
    Contradiction(ClickProposition),
    CloseInvariants,
    Rewrite(ClickProposition),
    Transport {
        source: ClickProposition,
        target: ClickProposition,
    },
    TransportUsing {
        source: ClickProposition,
        target: ClickProposition,
        premises: Vec<ClickProposition>,
    },
    InstantiateUsing {
        quantified: ClickProposition,
        argument: ContractExpression,
        premises: Vec<ClickProposition>,
    },
    Simp,
    SimpUsing(ProofSimpUsing),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SimpleTactic {
    Mark,
    StatementTransition,
    UnfoldPredicate,
    UnfoldResource,
    ObserveResource,
    Induct,
    ApplyInduction,
    CloseInduction,
    ApplyTheorem,
    Witness,
    Choose,
    Assumption,
    Extract,
    Normalize,
    Intro,
    Split,
    Left,
    Right,
    Enumerate,
    Contradiction,
    CloseInvariants,
    Rewrite,
    FactTransport,
    Instantiate,
    FoldResource,
    Frame,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SmartTacticKind {
    Auto,
    ApplyTheorem,
    FactTransport,
    SmartExecute,
    ExecuteUntil,
    Frame,
    Simp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlFlowTactic {
    Have,
    Open,
    If,
    Cases,
    Branch,
    Loop,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TacticClass {
    Simple(SimpleTactic),
    Smart(SmartTacticKind),
    ControlFlow(ControlFlowTactic),
}

/// One user-selectable proof-tactic form exposed by the Surface Click parser.
/// Internal planner-only variants don't appear in this registry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PublicTacticForm {
    pub id: &'static str,
    pub syntax: &'static str,
    pub class: &'static str,
}

/// Canonical public tactic forms used by the reference coverage test.
pub const PUBLIC_TACTIC_FORMS: &[PublicTacticForm] = &[
    PublicTacticForm {
        id: "mark",
        syntax: "mark name;",
        class: "simple",
    },
    PublicTacticForm {
        id: "step",
        syntax: "step()",
        class: "simple",
    },
    PublicTacticForm {
        id: "execute",
        syntax: "execute()",
        class: "smart",
    },
    PublicTacticForm {
        id: "execute-until",
        syntax: "execute_until",
        class: "smart",
    },
    PublicTacticForm {
        id: "frame",
        syntax: "frame()",
        class: "smart",
    },
    PublicTacticForm {
        id: "frame-using",
        syntax: "frame() using",
        class: "simple",
    },
    PublicTacticForm {
        id: "unfold-predicate",
        syntax: "unfold(name)",
        class: "simple",
    },
    PublicTacticForm {
        id: "unfold-resource",
        syntax: "unfold(name)",
        class: "simple",
    },
    PublicTacticForm {
        id: "fold-resource",
        syntax: "fold(resource)",
        class: "simple",
    },
    PublicTacticForm {
        id: "induct",
        syntax: "induct(n) as ih",
        class: "simple",
    },
    PublicTacticForm {
        id: "apply-induction",
        syntax: "apply(ih(m))",
        class: "simple",
    },
    PublicTacticForm {
        id: "apply-theorem",
        syntax: "apply(theorem(args))",
        class: "smart",
    },
    PublicTacticForm {
        id: "apply-theorem-using",
        syntax: "apply(theorem(args)) using",
        class: "simple",
    },
    PublicTacticForm {
        id: "have",
        syntax: "have P by",
        class: "control",
    },
    PublicTacticForm {
        id: "open",
        syntax: "open(resource)",
        class: "control",
    },
    PublicTacticForm {
        id: "if",
        syntax: "if P",
        class: "control",
    },
    PublicTacticForm {
        id: "cases",
        syntax: "cases (A or B)",
        class: "control",
    },
    PublicTacticForm {
        id: "branch",
        syntax: "branch",
        class: "control",
    },
    PublicTacticForm {
        id: "loop",
        syntax: "loop",
        class: "control",
    },
    PublicTacticForm {
        id: "observe-resource",
        syntax: "observe(resource)",
        class: "simple",
    },
    PublicTacticForm {
        id: "witness",
        syntax: "witness(name = value)",
        class: "simple",
    },
    PublicTacticForm {
        id: "choose",
        syntax: "choose(name from requirement(label))",
        class: "simple",
    },
    PublicTacticForm {
        id: "assumption",
        syntax: "assumption()",
        class: "simple",
    },
    PublicTacticForm {
        id: "extract",
        syntax: "extract(P)",
        class: "simple",
    },
    PublicTacticForm {
        id: "normalize",
        syntax: "normalize()",
        class: "simple",
    },
    PublicTacticForm {
        id: "intro",
        syntax: "intro()",
        class: "simple",
    },
    PublicTacticForm {
        id: "split",
        syntax: "split()",
        class: "simple",
    },
    PublicTacticForm {
        id: "left",
        syntax: "left()",
        class: "simple",
    },
    PublicTacticForm {
        id: "right",
        syntax: "right()",
        class: "simple",
    },
    PublicTacticForm {
        id: "enumerate",
        syntax: "enumerate()",
        class: "simple",
    },
    PublicTacticForm {
        id: "contradiction",
        syntax: "contradiction(P)",
        class: "simple",
    },
    PublicTacticForm {
        id: "close-invariants",
        syntax: "close_invariants()",
        class: "simple",
    },
    PublicTacticForm {
        id: "rewrite",
        syntax: "rewrite(P)",
        class: "simple",
    },
    PublicTacticForm {
        id: "transport",
        syntax: "transport(P, Q)",
        class: "smart",
    },
    PublicTacticForm {
        id: "transport-using",
        syntax: "transport(P, Q) using",
        class: "simple",
    },
    PublicTacticForm {
        id: "instantiate-using",
        syntax: "instantiate(F, value) using",
        class: "simple",
    },
    PublicTacticForm {
        id: "simp",
        syntax: "simp()",
        class: "smart",
    },
    PublicTacticForm {
        id: "simp-using",
        syntax: "simp() using",
        class: "smart",
    },
];

/// A structured proof containing only surface-expressible simple tactics.
///
/// Unlike [`ProofTactic`], this type cannot contain smart tactics or
/// internal-only implementation operations. Smart tactics should ultimately
/// return this type directly; printing it is then a structural conversion
/// back to ordinary `.click` syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofCertificate {
    steps: Vec<ProofStep>,
}

/// One explicit, surface-expressible step in a [`ProofCertificate`].
///
/// Unlike [`ProofTactic`], this representation has no smart-tactic variants.
/// Structured steps own recursively explicit child certificates, so a
/// certificate's checkable shape is enforced by the Rust type rather than
/// recovered later from [`ProofTactic::class`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofStep {
    Mark(String),
    Step,
    UnfoldPredicate(String),
    UnfoldResource(ResourceClause),
    FoldResource(ResourceClause),
    Induct {
        parameter: String,
        hypothesis: String,
    },
    ApplyInduction {
        hypothesis: String,
        argument: ContractExpression,
    },
    CloseInduction,
    ApplyTheoremUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    ObserveResource(ResourceClause),
    Witness(ProofWitness),
    Choose(ProofChoice),
    Assumption,
    Extract(ClickProposition),
    Normalize,
    Intro,
    Split,
    Left,
    Right,
    Enumerate,
    Contradiction(ClickProposition),
    CloseInvariants,
    Rewrite(ClickProposition),
    TransportUsing {
        source: ClickProposition,
        target: ClickProposition,
        premises: Vec<ClickProposition>,
    },
    InstantiateUsing {
        quantified: ClickProposition,
        argument: ContractExpression,
        premises: Vec<ClickProposition>,
    },
    FrameUsing {
        region: Option<CodeRegionRef>,
        premises: Vec<ClickProposition>,
    },
    Have {
        proposition: ClickProposition,
        proof: Box<ProofCertificate>,
    },
    Open {
        resource: ResourceClause,
        proof: Box<ProofCertificate>,
    },
    If {
        condition: ClickProposition,
        then_proof: Box<ProofCertificate>,
        else_proof: Box<ProofCertificate>,
    },
    Cases {
        disjunction: ClickProposition,
        left_proof: Box<ProofCertificate>,
        right_proof: Box<ProofCertificate>,
    },
    Branch {
        ensuring: Option<Vec<ProofAssertion>>,
        then_proof: Box<ProofCertificate>,
        else_proof: Box<ProofCertificate>,
    },
    Loop(CertificateStructuralClause),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateStructuralClause {
    region: CodeRegion,
    label: Option<String>,
    decreases: Option<ContractExpression>,
    items: Vec<CertificateStructuralItem>,
    initialize_proof: Option<Box<ProofCertificate>>,
    preserve_proof: Option<Box<ProofCertificate>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CertificateStructuralItem {
    kind: StructuralItemKind,
    claim: StructuralItemClaim,
    /// Invariants are declarations whose initialize/preserve proofs live on
    /// the enclosing loop. Effect items contain their own explicit proof.
    effect_proof: Option<Box<ProofCertificate>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificatePathSegment {
    Tactic(usize),
    HaveBody,
    OpenBody,
    ThenBranch,
    ElseBranch,
    LeftCase,
    RightCase,
    LoopInitialize,
    LoopPreserve,
    LoopItem(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateError {
    tactic_class: TacticClass,
    path: Vec<CertificatePathSegment>,
}

impl ProofCertificate {
    pub fn from_proof_tactics(tactics: &[ProofTactic]) -> Result<Self, CertificateError> {
        validate_certificate_tactics(tactics, &mut Vec::new())?;
        Ok(Self {
            steps: tactics
                .iter()
                .map(ProofStep::from_validated_tactic)
                .collect(),
        })
    }

    pub fn steps(&self) -> &[ProofStep] {
        &self.steps
    }

    pub(crate) fn from_steps(steps: Vec<ProofStep>) -> Self {
        Self { steps }
    }

    pub fn to_proof_tactics(&self) -> Vec<ProofTactic> {
        self.steps.iter().map(ProofStep::to_proof_tactic).collect()
    }

    fn from_validated_proof(proof: &SourceProof) -> Self {
        let SourceProof::Script(tactics) = proof else {
            unreachable!("validated simple proof must be an explicit script")
        };
        Self {
            steps: tactics
                .iter()
                .map(ProofStep::from_validated_tactic)
                .collect(),
        }
    }

    fn to_source_proof(&self) -> SourceProof {
        SourceProof::Script(self.to_proof_tactics())
    }
}

impl ProofStep {
    fn from_validated_tactic(tactic: &ProofTactic) -> Self {
        match tactic {
            ProofTactic::Mark(name) => Self::Mark(name.clone()),
            ProofTactic::Step => Self::Step,
            ProofTactic::UnfoldPredicate(name) => Self::UnfoldPredicate(name.clone()),
            ProofTactic::UnfoldResource(resource) => Self::UnfoldResource(resource.clone()),
            ProofTactic::FoldResource(resource) => Self::FoldResource(resource.clone()),
            ProofTactic::Induct {
                parameter,
                hypothesis,
            } => Self::Induct {
                parameter: parameter.clone(),
                hypothesis: hypothesis.clone(),
            },
            ProofTactic::ApplyInduction {
                hypothesis,
                argument,
            } => Self::ApplyInduction {
                hypothesis: hypothesis.clone(),
                argument: argument.clone(),
            },
            ProofTactic::CloseInduction => Self::CloseInduction,
            ProofTactic::ApplyTheoremUsing {
                application,
                premises,
            } => Self::ApplyTheoremUsing {
                application: application.clone(),
                premises: premises.clone(),
            },
            ProofTactic::ObserveResource(resource) => Self::ObserveResource(resource.clone()),
            ProofTactic::Witness(witness) => Self::Witness(witness.clone()),
            ProofTactic::Choose(choice) => Self::Choose(choice.clone()),
            ProofTactic::Assumption => Self::Assumption,
            ProofTactic::Extract(proposition) => Self::Extract(proposition.clone()),
            ProofTactic::Normalize => Self::Normalize,
            ProofTactic::Intro => Self::Intro,
            ProofTactic::Split => Self::Split,
            ProofTactic::Left => Self::Left,
            ProofTactic::Right => Self::Right,
            ProofTactic::Enumerate => Self::Enumerate,
            ProofTactic::Contradiction(proposition) => Self::Contradiction(proposition.clone()),
            ProofTactic::CloseInvariants => Self::CloseInvariants,
            ProofTactic::Rewrite(proposition) => Self::Rewrite(proposition.clone()),
            ProofTactic::TransportUsing {
                source,
                target,
                premises,
            } => Self::TransportUsing {
                source: source.clone(),
                target: target.clone(),
                premises: premises.clone(),
            },
            ProofTactic::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => Self::InstantiateUsing {
                quantified: quantified.clone(),
                argument: argument.clone(),
                premises: premises.clone(),
            },
            ProofTactic::FrameUsing { region, premises } => Self::FrameUsing {
                region: region.clone(),
                premises: premises.clone(),
            },
            ProofTactic::Have(proof_have) => Self::Have {
                proposition: proof_have.proposition.clone(),
                proof: Box::new(ProofCertificate::from_validated_proof(&proof_have.proof)),
            },
            ProofTactic::Open(proof_open) => Self::Open {
                resource: proof_open.resource.clone(),
                proof: Box::new(ProofCertificate {
                    steps: proof_open
                        .tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
            },
            ProofTactic::If(proof_if) => Self::If {
                condition: proof_if.condition.clone(),
                then_proof: Box::new(ProofCertificate {
                    steps: proof_if
                        .then_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
                else_proof: Box::new(ProofCertificate {
                    steps: proof_if
                        .else_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
            },
            ProofTactic::Cases(proof_cases) => Self::Cases {
                disjunction: proof_cases.disjunction.clone(),
                left_proof: Box::new(ProofCertificate {
                    steps: proof_cases
                        .left_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
                right_proof: Box::new(ProofCertificate {
                    steps: proof_cases
                        .right_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
            },
            ProofTactic::Branch(proof_branch) => Self::Branch {
                ensuring: proof_branch.ensuring.clone(),
                then_proof: Box::new(ProofCertificate {
                    steps: proof_branch
                        .then_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
                else_proof: Box::new(ProofCertificate {
                    steps: proof_branch
                        .else_tactics
                        .iter()
                        .map(Self::from_validated_tactic)
                        .collect(),
                }),
            },
            ProofTactic::Loop(clause) => Self::Loop(CertificateStructuralClause {
                region: clause.region,
                label: clause.label.clone(),
                decreases: clause.decreases.clone(),
                items: clause
                    .items
                    .iter()
                    .map(|item| CertificateStructuralItem {
                        kind: item.kind,
                        claim: item.claim.clone(),
                        effect_proof: item
                            .is_effect_kind()
                            .then(|| Box::new(ProofCertificate::from_validated_proof(&item.proof))),
                    })
                    .collect(),
                initialize_proof: clause
                    .initialize_proof
                    .as_ref()
                    .map(|proof| Box::new(ProofCertificate::from_validated_proof(proof))),
                preserve_proof: clause
                    .preserve_proof
                    .as_ref()
                    .map(|proof| Box::new(ProofCertificate::from_validated_proof(proof))),
            }),
            _ => unreachable!("certificate validation admitted a non-surface tactic"),
        }
    }

    fn to_proof_tactic(&self) -> ProofTactic {
        match self {
            Self::Mark(name) => ProofTactic::Mark(name.clone()),
            Self::Step => ProofTactic::Step,
            Self::UnfoldPredicate(name) => ProofTactic::UnfoldPredicate(name.clone()),
            Self::UnfoldResource(resource) => ProofTactic::UnfoldResource(resource.clone()),
            Self::FoldResource(resource) => ProofTactic::FoldResource(resource.clone()),
            Self::Induct {
                parameter,
                hypothesis,
            } => ProofTactic::Induct {
                parameter: parameter.clone(),
                hypothesis: hypothesis.clone(),
            },
            Self::ApplyInduction {
                hypothesis,
                argument,
            } => ProofTactic::ApplyInduction {
                hypothesis: hypothesis.clone(),
                argument: argument.clone(),
            },
            Self::CloseInduction => ProofTactic::CloseInduction,
            Self::ApplyTheoremUsing {
                application,
                premises,
            } => ProofTactic::ApplyTheoremUsing {
                application: application.clone(),
                premises: premises.clone(),
            },
            Self::ObserveResource(resource) => ProofTactic::ObserveResource(resource.clone()),
            Self::Witness(witness) => ProofTactic::Witness(witness.clone()),
            Self::Choose(choice) => ProofTactic::Choose(choice.clone()),
            Self::Assumption => ProofTactic::Assumption,
            Self::Extract(proposition) => ProofTactic::Extract(proposition.clone()),
            Self::Normalize => ProofTactic::Normalize,
            Self::Intro => ProofTactic::Intro,
            Self::Split => ProofTactic::Split,
            Self::Left => ProofTactic::Left,
            Self::Right => ProofTactic::Right,
            Self::Enumerate => ProofTactic::Enumerate,
            Self::Contradiction(proposition) => ProofTactic::Contradiction(proposition.clone()),
            Self::CloseInvariants => ProofTactic::CloseInvariants,
            Self::Rewrite(proposition) => ProofTactic::Rewrite(proposition.clone()),
            Self::TransportUsing {
                source,
                target,
                premises,
            } => ProofTactic::TransportUsing {
                source: source.clone(),
                target: target.clone(),
                premises: premises.clone(),
            },
            Self::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => ProofTactic::InstantiateUsing {
                quantified: quantified.clone(),
                argument: argument.clone(),
                premises: premises.clone(),
            },
            Self::FrameUsing { region, premises } => ProofTactic::FrameUsing {
                region: region.clone(),
                premises: premises.clone(),
            },
            Self::Have { proposition, proof } => ProofTactic::Have(ProofHave {
                proposition: proposition.clone(),
                proof: proof.to_source_proof(),
            }),
            Self::Open { resource, proof } => ProofTactic::Open(ProofOpen {
                resource: resource.clone(),
                tactics: proof.to_proof_tactics(),
            }),
            Self::If {
                condition,
                then_proof,
                else_proof,
            } => ProofTactic::If(ProofIf {
                condition: condition.clone(),
                then_tactics: then_proof.to_proof_tactics(),
                else_tactics: else_proof.to_proof_tactics(),
            }),
            Self::Cases {
                disjunction,
                left_proof,
                right_proof,
            } => ProofTactic::Cases(ProofCases {
                disjunction: disjunction.clone(),
                left_tactics: left_proof.to_proof_tactics(),
                right_tactics: right_proof.to_proof_tactics(),
            }),
            Self::Branch {
                ensuring,
                then_proof,
                else_proof,
            } => ProofTactic::Branch(ProofBranch {
                ensuring: ensuring.clone(),
                then_tactics: then_proof.to_proof_tactics(),
                else_tactics: else_proof.to_proof_tactics(),
            }),
            Self::Loop(clause) => ProofTactic::Loop(StructuralClause {
                region: clause.region,
                label: clause.label.clone(),
                decreases: clause.decreases.clone(),
                items: clause
                    .items
                    .iter()
                    .map(|item| StructuralItem {
                        kind: item.kind,
                        claim: item.claim.clone(),
                        proof: item
                            .effect_proof
                            .as_ref()
                            .map(|proof| proof.to_source_proof())
                            .unwrap_or(SourceProof::Tactic(SmartTactic::Auto)),
                    })
                    .collect(),
                initialize_proof: clause
                    .initialize_proof
                    .as_ref()
                    .map(|proof| proof.to_source_proof()),
                preserve_proof: clause
                    .preserve_proof
                    .as_ref()
                    .map(|proof| proof.to_source_proof()),
            }),
        }
    }
}

impl CertificateError {
    pub fn tactic_class(&self) -> TacticClass {
        self.tactic_class
    }

    pub fn path(&self) -> &[CertificatePathSegment] {
        &self.path
    }
}

fn validate_certificate_tactics(
    tactics: &[ProofTactic],
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    for (index, tactic) in tactics.iter().enumerate() {
        path.push(CertificatePathSegment::Tactic(index));
        let result = match tactic.class() {
            TacticClass::Simple(_) => Ok(()),
            tactic_class @ TacticClass::Smart(_) => Err(CertificateError {
                tactic_class,
                path: path.clone(),
            }),
            TacticClass::ControlFlow(ControlFlowTactic::Have) => {
                let ProofTactic::Have(proof_have) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::HaveBody);
                let result = validate_certificate_proof(&proof_have.proof, path);
                path.pop();
                result
            }
            TacticClass::ControlFlow(ControlFlowTactic::Open) => {
                let ProofTactic::Open(proof_open) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::OpenBody);
                let result = validate_certificate_tactics(&proof_open.tactics, path);
                path.pop();
                result
            }
            TacticClass::ControlFlow(ControlFlowTactic::If) => {
                let ProofTactic::If(proof_if) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::ThenBranch);
                let then_result = validate_certificate_tactics(&proof_if.then_tactics, path);
                path.pop();
                if then_result.is_err() {
                    then_result
                } else {
                    path.push(CertificatePathSegment::ElseBranch);
                    let else_result = validate_certificate_tactics(&proof_if.else_tactics, path);
                    path.pop();
                    else_result
                }
            }
            TacticClass::ControlFlow(ControlFlowTactic::Cases) => {
                let ProofTactic::Cases(proof_cases) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::LeftCase);
                let left_result = validate_certificate_tactics(&proof_cases.left_tactics, path);
                path.pop();
                if left_result.is_err() {
                    left_result
                } else {
                    path.push(CertificatePathSegment::RightCase);
                    let right_result =
                        validate_certificate_tactics(&proof_cases.right_tactics, path);
                    path.pop();
                    right_result
                }
            }
            TacticClass::ControlFlow(ControlFlowTactic::Branch) => {
                let ProofTactic::Branch(proof_branch) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::ThenBranch);
                let then_result = validate_certificate_tactics(&proof_branch.then_tactics, path);
                path.pop();
                if then_result.is_err() {
                    then_result
                } else {
                    path.push(CertificatePathSegment::ElseBranch);
                    let else_result =
                        validate_certificate_tactics(&proof_branch.else_tactics, path);
                    path.pop();
                    else_result
                }
            }
            TacticClass::ControlFlow(ControlFlowTactic::Loop) => {
                let ProofTactic::Loop(loop_clause) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                let mut result;
                path.push(CertificatePathSegment::LoopInitialize);
                result = match loop_clause.initialize_proof() {
                    Some(proof) => validate_certificate_proof(proof, path),
                    None => Err(CertificateError {
                        tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
                        path: path.clone(),
                    }),
                };
                path.pop();
                if result.is_ok() {
                    path.push(CertificatePathSegment::LoopPreserve);
                    result = match loop_clause.preserve_proof() {
                        Some(proof) => validate_certificate_proof(proof, path),
                        None => Err(CertificateError {
                            tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
                            path: path.clone(),
                        }),
                    };
                    path.pop();
                }
                if result.is_ok() {
                    for (item_index, item) in loop_clause.items().iter().enumerate() {
                        if !item.is_effect_kind() {
                            continue;
                        }
                        path.push(CertificatePathSegment::LoopItem(item_index));
                        result = validate_certificate_proof(item.proof(), path);
                        path.pop();
                        if result.is_err() {
                            break;
                        }
                    }
                }
                result
            }
        };
        path.pop();
        result?;
    }
    Ok(())
}

fn validate_certificate_proof(
    proof: &SourceProof,
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    match proof {
        SourceProof::Default => Err(CertificateError {
            tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
            path: path.clone(),
        }),
        SourceProof::Tactic(smart_tactic) => Err(CertificateError {
            tactic_class: TacticClass::Smart(smart_tactic.kind()),
            path: path.clone(),
        }),
        SourceProof::Script(tactics) => validate_certificate_tactics(tactics, path),
    }
}

impl ProofTactic {
    pub fn class(&self) -> TacticClass {
        match self {
            Self::Mark(_) => TacticClass::Simple(SimpleTactic::Mark),
            Self::Step => TacticClass::Simple(SimpleTactic::StatementTransition),
            Self::UnfoldPredicate(_) => TacticClass::Simple(SimpleTactic::UnfoldPredicate),
            Self::UnfoldResource(_) => TacticClass::Simple(SimpleTactic::UnfoldResource),
            Self::ObserveResource(_) => TacticClass::Simple(SimpleTactic::ObserveResource),
            Self::Induct { .. } => TacticClass::Simple(SimpleTactic::Induct),
            Self::ApplyInduction { .. } => TacticClass::Simple(SimpleTactic::ApplyInduction),
            Self::CloseInduction => TacticClass::Simple(SimpleTactic::CloseInduction),
            Self::ApplyTheorem(_) => TacticClass::Smart(SmartTacticKind::ApplyTheorem),
            Self::ApplyTheoremUsing { .. } => TacticClass::Simple(SimpleTactic::ApplyTheorem),
            Self::Witness(_) => TacticClass::Simple(SimpleTactic::Witness),
            Self::Choose(_) => TacticClass::Simple(SimpleTactic::Choose),
            Self::Assumption => TacticClass::Simple(SimpleTactic::Assumption),
            Self::Extract(_) => TacticClass::Simple(SimpleTactic::Extract),
            Self::Normalize => TacticClass::Simple(SimpleTactic::Normalize),
            Self::Intro => TacticClass::Simple(SimpleTactic::Intro),
            Self::Split => TacticClass::Simple(SimpleTactic::Split),
            Self::Left => TacticClass::Simple(SimpleTactic::Left),
            Self::Right => TacticClass::Simple(SimpleTactic::Right),
            Self::Enumerate => TacticClass::Simple(SimpleTactic::Enumerate),
            Self::Contradiction(_) => TacticClass::Simple(SimpleTactic::Contradiction),
            Self::CloseInvariants => TacticClass::Simple(SimpleTactic::CloseInvariants),
            Self::Rewrite(_) => TacticClass::Simple(SimpleTactic::Rewrite),
            Self::Transport { .. } => TacticClass::Smart(SmartTacticKind::FactTransport),
            Self::TransportUsing { .. } => TacticClass::Simple(SimpleTactic::FactTransport),
            Self::InstantiateUsing { .. } => TacticClass::Simple(SimpleTactic::Instantiate),
            Self::FoldResource(_) => TacticClass::Simple(SimpleTactic::FoldResource),
            Self::FrameUsing { .. } => TacticClass::Simple(SimpleTactic::Frame),
            Self::SmartExecute | Self::SmartExecuteAllPaths => {
                TacticClass::Smart(SmartTacticKind::SmartExecute)
            }
            Self::ExecuteUntil(_) => TacticClass::Smart(SmartTacticKind::ExecuteUntil),
            Self::SmartFrame(_) => TacticClass::Smart(SmartTacticKind::Frame),
            Self::Simp => TacticClass::Smart(SmartTacticKind::Simp),
            Self::SimpUsing(_) => TacticClass::Smart(SmartTacticKind::Simp),
            Self::Have(_) => TacticClass::ControlFlow(ControlFlowTactic::Have),
            Self::Open(_) => TacticClass::ControlFlow(ControlFlowTactic::Open),
            Self::If(_) => TacticClass::ControlFlow(ControlFlowTactic::If),
            Self::Cases(_) => TacticClass::ControlFlow(ControlFlowTactic::Cases),
            Self::Branch(_) => TacticClass::ControlFlow(ControlFlowTactic::Branch),
            Self::Loop(_) => TacticClass::ControlFlow(ControlFlowTactic::Loop),
        }
    }
}

impl SmartTactic {
    pub fn kind(self) -> SmartTacticKind {
        match self {
            Self::Auto => SmartTacticKind::Auto,
            Self::Frame => SmartTacticKind::Frame,
            Self::Simp => SmartTacticKind::Simp,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofHave {
    proposition: ClickProposition,
    proof: SourceProof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofOpen {
    resource: ResourceClause,
    tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofIf {
    condition: ClickProposition,
    then_tactics: Vec<ProofTactic>,
    else_tactics: Vec<ProofTactic>,
}

/// Explicit elimination of a disjunctive fact: proof checking requires the written
/// disjunction is an available fact, then checks each branch under exactly its
/// assumed disjunct. Both branches are always written; nothing is searched.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofCases {
    disjunction: ClickProposition,
    left_tactics: Vec<ProofTactic>,
    right_tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofBranch {
    ensuring: Option<Vec<ProofAssertion>>,
    then_tactics: Vec<ProofTactic>,
    else_tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofSimpUsing {
    premises: Vec<ClickProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofAssertion {
    Fact(ClickProposition),
    Resource(ResourceClause),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TheoremApplication {
    name: String,
    arguments: Vec<ContractExpression>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum CodeRegionRef {
    Function,
    Loop(usize),
    Statement(usize),
    Label(String),
}

/// A proof-visible name for one recorded symbolic state.
///
/// Program points are locations in C. Marks are proof-local names bound to
/// the current state, so they deliberately remain a separate variant rather
/// than masquerading as C code regions.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum SnapshotSelector {
    ProgramPoint(ProgramPointRef),
    Mark(String),
}

impl From<ProgramPointRef> for SnapshotSelector {
    fn from(point: ProgramPointRef) -> Self {
        Self::ProgramPoint(point)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct ProgramPointRef {
    region: CodeRegionRef,
    kind: ProgramPointKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum ProgramPointKind {
    Entry,
    Exit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofWitness {
    name: String,
    value: ContractExpression,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofChoice {
    name: String,
    source: ProofFactSource,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofFactSource {
    Requirement(usize),
    RequirementLabel(String),
}

/// A `.click` tactic that may search for a proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SmartTactic {
    Auto,
    Frame,
    Simp,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PredicateEnvironment {
    definitions: BTreeMap<String, PredicateDefinition>,
}

impl PredicateEnvironment {
    fn new(definitions: &[PredicateDefinition]) -> Self {
        Self {
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
        }
    }

    fn get(&self, name: &str) -> Option<&PredicateDefinition> {
        self.definitions.get(name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClickFunctionEnvironment {
    definitions: BTreeMap<String, ClickFunctionDefinition>,
}

impl ClickFunctionEnvironment {
    fn new(definitions: &[ClickFunctionDefinition]) -> Self {
        Self {
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
        }
    }

    fn get(&self, name: &str) -> Option<&ClickFunctionDefinition> {
        self.definitions.get(name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResourceEnvironment {
    definitions: BTreeMap<String, ResourceDefinition>,
}

impl ResourceEnvironment {
    fn new(definitions: &[ResourceDefinition]) -> Self {
        Self {
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
        }
    }

    fn get(&self, name: &str) -> Option<&ResourceDefinition> {
        self.definitions.get(name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TheoremEnvironment {
    definitions: BTreeMap<String, TheoremDefinition>,
}

impl TheoremEnvironment {
    fn new(definitions: &[TheoremDefinition]) -> Self {
        Self {
            definitions: definitions
                .iter()
                .map(|definition| (definition.name().to_string(), definition.clone()))
                .collect(),
        }
    }

    fn get(&self, name: &str) -> Option<&TheoremDefinition> {
        self.definitions.get(name)
    }

    fn insert(&mut self, definition: TheoremDefinition) {
        self.definitions
            .insert(definition.name().to_string(), definition);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedCTheorem {
    pub source_path: String,
    pub function_block: FunctionBlock,
    pub claim: VerifiedClaim,
    pub proof_kind: ProofKind,
    pub proof_tactics: Option<Vec<ProofTactic>>,
    pub expanded_proof: Option<ProofCertificate>,
    pub expansion_blocker: Option<String>,
    pub specification: CFunctionSpecification,
    pub theorem: Theorem,
    pub concrete_loop_execution: bool,
    pub(crate) checked_execution: CCheckedFunctionExecution,
    pub(crate) frontier_loop_clauses: Vec<StructuralClause>,
    pub(crate) frontier_loop_rules: Vec<CVerifiedLoopRule>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedPureTheorem {
    pub theorem_definition: TheoremDefinition,
    pub ensure_index: usize,
    pub ensure_clause: EnsureClause,
    pub proof_kind: ProofKind,
    pub proof: Option<ProofCertificate>,
    pub requires: Vec<Proposition>,
    pub conclusion: Proposition,
    pub(crate) kernel_authority: Option<CVerifiedPureTheorem>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VerifiedClaim {
    Ensure { index: usize, clause: EnsureClause },
    Effect { index: usize, clause: EffectClause },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofKind {
    Axiom,
    Pure,
    Frame,
    Simp,
    TacticScript,
    LoopVerification,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickError {
    message: String,
    timing_tactic: Option<TimingTacticContext>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TimingTacticContext {
    claim_label: String,
    tactic_index: usize,
    tactic_name: String,
    tactic_class: String,
    statement_index: usize,
    source_index: usize,
}

thread_local! {
    static ACTIVE_TIMING_TACTICS: std::cell::RefCell<Vec<TimingTacticContext>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

fn push_timing_tactic(context: TimingTacticContext) {
    ACTIVE_TIMING_TACTICS.with(|active| active.borrow_mut().push(context));
}

fn pop_timing_tactic(context: &TimingTacticContext) {
    ACTIVE_TIMING_TACTICS.with(|active| {
        let mut active = active.borrow_mut();
        if let Some(index) = active.iter().rposition(|candidate| candidate == context) {
            active.remove(index);
        }
    });
}

fn current_timing_tactic() -> Option<TimingTacticContext> {
    ACTIVE_TIMING_TACTICS.with(|active| active.borrow().last().cloned())
}

#[derive(Clone)]
pub struct C0VerificationSession {
    c_sources: Vec<(String, String)>,
    baseline_file: ClickFile,
    verified_function_environment: CExecutionEnvironment,
}

impl ClickFile {
    pub fn verifying_sources(&self) -> &[String] {
        &self.verifying_sources
    }

    pub fn predicate_definitions(&self) -> &[PredicateDefinition] {
        &self.predicate_definitions
    }

    pub fn click_function_definitions(&self) -> &[ClickFunctionDefinition] {
        &self.click_function_definitions
    }

    pub fn resource_definitions(&self) -> &[ResourceDefinition] {
        &self.resource_definitions
    }

    pub fn theorem_definitions(&self) -> &[TheoremDefinition] {
        &self.theorem_definitions
    }

    pub fn function_blocks(&self) -> &[FunctionBlock] {
        &self.function_blocks
    }
}

impl PredicateDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn body(&self) -> &ClickProposition {
        &self.body
    }
}

impl ClickFunctionDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn decreases(&self) -> Option<&ContractExpression> {
        self.decreases.as_ref()
    }

    pub fn body(&self) -> &ContractExpression {
        &self.body
    }
}

impl ResourceDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn composite_body(&self) -> Option<&CompositeResourceBody> {
        self.composite_body.as_ref()
    }
}

impl CompositeResourceBody {
    pub fn condition(&self) -> Option<&ClickProposition> {
        self.condition.as_ref()
    }

    pub fn contains(&self) -> &[ResourceClause] {
        &self.contains
    }

    pub fn facts(&self) -> &[ClickProposition] {
        &self.facts
    }
}

impl TheoremDefinition {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    pub fn ensures(&self) -> &[EnsureClause] {
        &self.ensures
    }
}

impl FunctionBlock {
    pub fn signature(&self) -> &FunctionSignature {
        &self.signature
    }

    pub fn requires(&self) -> &[Requirement] {
        &self.requires
    }

    pub(in crate::lang::click) fn requirement_label_indices(&self) -> &BTreeMap<String, usize> {
        &self.requirement_label_indices
    }

    pub fn decreases(&self) -> Option<&CFunctionDecrease> {
        self.decreases.as_ref()
    }

    pub fn structural_clauses(&self) -> &[StructuralClause] {
        &self.structural_clauses
    }

    pub fn effects(&self) -> &[EffectClause] {
        &self.effects
    }

    pub fn ensures(&self) -> &[EnsureClause] {
        &self.ensures
    }

    pub fn grouped_proof(&self) -> Option<&SourceProof> {
        self.grouped_proof.as_ref()
    }

    fn with_frontier_loop_clause(&self, clause: &StructuralClause, loop_index: usize) -> Self {
        let mut function = self.clone();
        function
            .structural_clauses
            .push(clause.bound_to_loop(loop_index));
        function
    }

    fn with_bound_frontier_loop_clauses(&self, clauses: &[StructuralClause]) -> Self {
        let mut function = self.clone();
        function.structural_clauses.extend_from_slice(clauses);
        function
    }
}

impl FunctionSignature {
    fn declared_loadable_bytes(&self) -> &[(String, u32)] {
        &self.declared_loadable_bytes
    }

    pub fn return_type(&self) -> C0Type {
        self.return_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[FunctionParameter] {
        &self.parameters
    }
}

impl FunctionParameter {
    pub fn c_type(&self) -> C0Type {
        self.c_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn struct_name(&self) -> Option<&str> {
        self.struct_name.as_deref()
    }
}

impl Requirement {
    pub fn label(&self) -> Option<&str> {
        match self {
            Self::Labeled { label, .. } => Some(label),
            _ => None,
        }
    }

    fn inner(&self) -> &Requirement {
        match self {
            Self::Labeled { requirement, .. } => requirement.inner(),
            _ => self,
        }
    }

    fn proposition(&self) -> Option<&ClickProposition> {
        match self.inner() {
            Self::Proposition(proposition) => Some(proposition),
            _ => None,
        }
    }
}

fn requirement_contains_resource(requirement: &Requirement) -> bool {
    matches!(requirement.inner(), Requirement::Resource(_))
}

fn parameter_is_click_array_ref(parameter: &FunctionParameter) -> bool {
    matches!(
        parameter.c_type(),
        C0Type::Int32Pointer | C0Type::UInt8Pointer
    )
}

fn click_array_element_type(c_type: C0Type) -> Option<CType> {
    match c_type {
        C0Type::Int32Pointer | C0Type::Int32Array(_) => Some(CType::Int32),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => Some(CType::UInt8),
        C0Type::Void | C0Type::Int32 | C0Type::UInt8 => None,
    }
}

impl EnsureClause {
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn ensure(&self) -> &Ensure {
        &self.ensure
    }

    pub fn proof(&self) -> &SourceProof {
        &self.proof
    }
}

impl EffectClause {
    pub fn effect(&self) -> &Effect {
        &self.effect
    }

    pub fn proof(&self) -> &SourceProof {
        &self.proof
    }
}

impl StructuralClause {
    pub fn region(&self) -> &CodeRegion {
        &self.region
    }

    pub fn label(&self) -> Option<&str> {
        self.label.as_deref()
    }

    pub fn decreases(&self) -> Option<&ContractExpression> {
        self.decreases.as_ref()
    }

    pub fn items(&self) -> &[StructuralItem] {
        &self.items
    }

    pub fn initialize_proof(&self) -> Option<&SourceProof> {
        self.initialize_proof.as_ref()
    }

    pub fn preserve_proof(&self) -> Option<&SourceProof> {
        self.preserve_proof.as_ref()
    }

    fn bound_to_loop(&self, loop_index: usize) -> Self {
        let mut bound = self.clone();
        bound.region = CodeRegion::Loop(loop_index);
        bound
    }
}

impl StructuralItem {
    pub fn kind(&self) -> StructuralItemKind {
        self.kind
    }

    pub fn proposition(&self) -> Option<&ClickProposition> {
        match &self.claim {
            StructuralItemClaim::Proposition(proposition) => Some(proposition),
            StructuralItemClaim::Effect(_) => None,
        }
    }

    pub fn effect(&self) -> Option<&Effect> {
        match &self.claim {
            StructuralItemClaim::Effect(effect) => Some(effect),
            StructuralItemClaim::Proposition(_) => None,
        }
    }

    fn is_effect_kind(&self) -> bool {
        matches!(
            self.kind,
            StructuralItemKind::Effect | StructuralItemKind::StepEffect
        )
    }

    pub fn proof(&self) -> &SourceProof {
        &self.proof
    }
}

impl SourceProof {
    pub fn is_auto_tactic(&self) -> bool {
        matches!(self, Self::Default | Self::Tactic(SmartTactic::Auto))
    }

    pub fn is_frame_tactic(&self) -> bool {
        matches!(self, Self::Tactic(SmartTactic::Frame))
    }

    pub fn is_auto_or_frame_tactic(&self) -> bool {
        self.is_auto_tactic() || self.is_frame_tactic()
    }

    fn unfold_tactic_names(&self) -> Vec<String> {
        match self {
            Self::Default | Self::Tactic(_) => Vec::new(),
            Self::Script(tactics) => {
                let mut names = Vec::new();
                collect_unfold_tactic_names(tactics, &mut names);
                names
            }
        }
    }

    pub fn tactic(&self) -> Option<&SmartTactic> {
        match self {
            Self::Default => None,
            Self::Tactic(tactic) => Some(tactic),
            Self::Script(_) => None,
        }
    }

    pub fn tactics(&self) -> Option<&[ProofTactic]> {
        match self {
            Self::Default => None,
            Self::Tactic(_) => None,
            Self::Script(tactics) => Some(tactics),
        }
    }
}

fn collect_unfold_tactic_names(tactics: &[ProofTactic], names: &mut Vec<String>) {
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(name) => names.push(name.clone()),
            ProofTactic::Have(have) => {
                if let SourceProof::Script(tactics) = &have.proof {
                    collect_unfold_tactic_names(tactics, names);
                }
            }
            ProofTactic::Open(open) => collect_unfold_tactic_names(&open.tactics, names),
            ProofTactic::If(proof_if) => {
                collect_unfold_tactic_names(&proof_if.then_tactics, names);
                collect_unfold_tactic_names(&proof_if.else_tactics, names);
            }
            ProofTactic::Branch(branch) => {
                collect_unfold_tactic_names(&branch.then_tactics, names);
                collect_unfold_tactic_names(&branch.else_tactics, names);
            }
            _ => {}
        }
    }
}

impl VerifiedCTheorem {
    pub fn proof_kind(&self) -> ProofKind {
        self.proof_kind
    }

    pub fn proof_tactics(&self) -> Option<&[ProofTactic]> {
        self.proof_tactics.as_deref()
    }

    pub fn expanded_proof_tactics(&self) -> Option<Vec<ProofTactic>> {
        self.expanded_proof
            .as_ref()
            .map(ProofCertificate::to_proof_tactics)
    }

    pub fn expansion_blocker(&self) -> Option<&str> {
        self.expansion_blocker.as_deref()
    }

    pub fn expanded_proof_certificate(&self) -> Result<ProofCertificate, ClickError> {
        self.expanded_proof.clone().ok_or_else(|| {
            ClickError::new(format!(
                "proof expansion is unavailable for `{}`: {}",
                self.function_block.signature().name(),
                self.expansion_blocker
                    .as_deref()
                    .unwrap_or("verification did not record a surface expansion")
            ))
        })
    }

    pub fn expanded_proof_source(&self) -> Result<String, ClickError> {
        Ok(format_proof_certificate(
            &self.expanded_proof_certificate()?,
        ))
    }

    pub fn ensure_clause(&self) -> Option<&EnsureClause> {
        match &self.claim {
            VerifiedClaim::Ensure { clause, .. } => Some(clause),
            VerifiedClaim::Effect { .. } => None,
        }
    }

    pub fn effect_clause(&self) -> Option<&EffectClause> {
        match &self.claim {
            VerifiedClaim::Effect { clause, .. } => Some(clause),
            VerifiedClaim::Ensure { .. } => None,
        }
    }
}

impl VerifiedPureTheorem {
    pub fn proof_tactics(&self) -> Option<Vec<ProofTactic>> {
        self.proof.as_ref().map(ProofCertificate::to_proof_tactics)
    }

    pub fn proof_certificate(&self) -> Result<ProofCertificate, ClickError> {
        self.proof.clone().ok_or_else(|| {
            ClickError::new(format!(
                "pure theorem `{}` ensure {} has no surface certificate",
                self.theorem_definition.name(),
                self.ensure_index
            ))
        })
    }

    pub fn expanded_proof_source(&self) -> Result<String, ClickError> {
        Ok(format_proof_certificate(&self.proof_certificate()?))
    }
}

impl ClickError {
    fn new(message: impl Into<String>) -> Self {
        let message = message.into();
        let message = match crate::instrumentation::exceeded_verification_limit_context() {
            // Deliberate limit diagnostics already include the active context
            // and often add useful target/premise detail. Preserve those;
            // replace only an unrelated semantic error constructed from a
            // conservative false/none after the limit fired.
            Some(context) if !message.contains(&context) => {
                format!("verification budget exhausted inside {context}")
            }
            _ => message,
        };
        Self {
            message: diagnostics::bound_error_message(message),
            timing_tactic: current_timing_tactic(),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    fn emit_timing_failure(&self) {
        if !instrumentation::enabled() {
            return;
        }
        if let Some(tactic) = &self.timing_tactic {
            instrumentation::emit(VerificationEvent::TacticFailed(TacticEvent {
                claim: tactic.claim_label.clone(),
                tactic_index: tactic.tactic_index,
                tactic_name: tactic.tactic_name.clone(),
                class: tactic.tactic_class.clone(),
                statement_index: tactic.statement_index,
                source_index: tactic.source_index,
            }));
        }
    }
}

#[cfg(test)]
mod tests;
