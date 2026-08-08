//! Tiny `.click` sidecar verifier for the C0 kernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::instrumentation::{self, TacticEvent, VerificationEvent};
use crate::kernel::{
    Assumptions, Bitvector32Term, CComparisonOperator, CCompositeResourceDefinition,
    CConditionOutcome, CExecutionEnvironment, CExecutionSemantics, CExpression, CExpressionOutcome,
    CFunction, CFunctionContractClaim, CFunctionContractClaimKey, CFunctionContractClaimTarget,
    CFunctionContractExecutionMode, CFunctionExecutionCandidates, CFunctionOutcome,
    CFunctionSpecification, CLoopEffect, CLoopEffectCheck, CLoopEffectSpan, CLoopInvariantCheck,
    CMemory, CMemoryRange, CMemorySegment, CResource, CResourceAccessMode, CResourceFact,
    CResourceSpec, CState, CStatement, CStatementOutcome, CType, CValue, CVerifiedLoopRule,
    ConditionTerm, ExecutionBudget, ExecutionPureFact, Pointer, PointerBlock, PointerOffsetTerm,
    ProofObligation, Proposition, PropositionDerivation, ResourceContext,
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
    c_while_with_invariant_and_effect_checks, canonical_c_memory_for_pointer_load,
    certify_c_function_execution_path_resource_representation, conditions_equal_ignoring_memories,
    int32, prove_c_condition_fact_direct_transport, prove_c_condition_fact_transport,
    prove_c_function_contract_execution_paths_with_environment,
    prove_c_function_satisfies_specification_from_symbolic_path, prove_forall_int32_application,
    prove_symbolic_c_condition_evaluation,
    prove_symbolic_c_function_contract_verification_paths_with_environment,
    prove_symbolic_c_function_execution_paths_with_environment,
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget,
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget,
    substitute_int32_variable_in_proposition,
};
use crate::lang::c::syntax::{self, C0Expression, C0Type};

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
    c0_tactic_source_position, expand_c0_claim_source, expand_c0_tactic_source_at,
    verifying_source_paths,
};
use expansion::{ProofSite, VerificationTarget, verification_target_at};
use lowering::*;
use parser::ContractLetBinding;
pub use printing::{format_proof_tactics, format_tactic_certificate};
use proof::*;
use validation::{
    combined_click_function_definitions, combined_predicate_definitions,
    combined_resource_definitions, combined_theorem_definitions,
    combined_theorem_definitions_with_stdlib_ensure_count, contains_at_expression,
    contains_old_expression, describe_c0_type, describe_resource_clause,
    proposition_contains_at_expression,
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
    multiplicity: ResourceMultiplicity,
    composite_body: Option<CompositeResourceBody>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceMultiplicity {
    Exclusive,
    Counted,
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
    decreases: Option<CFunctionDecrease>,
    structural_clauses: Vec<StructuralClause>,
    effects: Vec<EffectClause>,
    ensures: Vec<EnsureClause>,
    grouped_proof: Option<Proof>,
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
    proof: Proof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectClause {
    effect: Effect,
    proof: Proof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralClause {
    region: CodeRegion,
    label: Option<String>,
    decreases: Option<ContractExpression>,
    items: Vec<StructuralItem>,
    initialize_proof: Option<Proof>,
    preserve_proof: Option<Proof>,
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
    proof: Proof,
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
    Read(ContractSegment),
    Write(ContractSegment),
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
    Counted,
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
        selector: VisitSelector,
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

/// Surface spellings paired with the exact kernel propositions they lowered
/// to in one proof context.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SurfacePropositionMap {
    by_kernel: BTreeMap<Proposition, Vec<ClickProposition>>,
    by_surface: Vec<(ClickProposition, Vec<Proposition>)>,
}

impl SurfacePropositionMap {
    pub fn record_lowering(
        &mut self,
        surface: &ClickProposition,
        kernel: &Proposition,
    ) -> Result<(), ClickError> {
        let spellings = self.by_kernel.entry(kernel.clone()).or_default();
        if !spellings.contains(surface) {
            spellings.push(surface.clone());
        }
        let lowerings = if let Some((_, lowerings)) = self
            .by_surface
            .iter_mut()
            .find(|(recorded, _)| recorded == surface)
        {
            lowerings
        } else {
            self.by_surface.push((surface.clone(), Vec::new()));
            &mut self
                .by_surface
                .last_mut()
                .expect("surface lowering was just inserted")
                .1
        };
        if !lowerings.contains(kernel) {
            lowerings.push(kernel.clone());
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

    pub fn surface(&self, kernel: &Proposition) -> Result<&ClickProposition, ClickError> {
        self.by_kernel
            .get(kernel)
            .and_then(|spellings| spellings.last())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "kernel proposition has no recorded Click surface spelling: {kernel:?}"
                ))
            })
    }

    pub fn surfaces(&self, kernel: &Proposition) -> impl Iterator<Item = &ClickProposition> {
        self.by_kernel
            .get(kernel)
            .into_iter()
            .flat_map(|spellings| spellings.iter())
    }

    pub fn kernel_facts(&self) -> impl Iterator<Item = &Proposition> {
        self.by_kernel.keys()
    }

    pub fn available_kernel(
        &self,
        surface: &ClickProposition,
        available: &[Proposition],
    ) -> Option<&Proposition> {
        let mut matches = self
            .by_surface
            .iter()
            .find_map(|(recorded, lowerings)| (recorded == surface).then_some(lowerings))?
            .iter()
            .filter(|kernel| available.contains(kernel));
        let kernel = matches.next()?;
        matches.next().is_none().then_some(kernel)
    }

    pub fn unique_kernel(&self, surface: &ClickProposition) -> Option<&Proposition> {
        let mut lowerings = self
            .by_surface
            .iter()
            .find_map(|(recorded, lowerings)| (recorded == surface).then_some(lowerings))?
            .iter();
        let kernel = lowerings.next()?;
        lowerings.next().is_none().then_some(kernel)
    }

    pub fn checked_surface<F>(
        &self,
        kernel: &Proposition,
        mut lower_at_current_point: F,
    ) -> Result<ClickProposition, ClickError>
    where
        F: FnMut(&ClickProposition) -> Result<Proposition, ClickError>,
    {
        let spellings = self.by_kernel.get(kernel).ok_or_else(|| {
            ClickError::new(format!(
                "kernel proposition has no recorded Click surface spelling: {kernel:?}"
            ))
        })?;
        let mut last_mismatch = None;
        for surface in spellings.iter().rev() {
            match lower_at_current_point(surface) {
                Ok(lowered) if &lowered == kernel => return Ok(surface.clone()),
                Ok(lowered) => last_mismatch = Some(format!("{surface:?} -> {lowered:?}")),
                Err(error) => last_mismatch = Some(format!("{surface:?} -> {}", error.message())),
            }
        }
        Err(ClickError::new(format!(
            "none of the recorded Click spellings lower to the proposition at the current proof point{}; expected {kernel:?}",
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
    Old(Box<ContractExpression>),
    At {
        selector: VisitSelector,
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
type ProgramPointStates = BTreeMap<ProgramPointRef, CState>;

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
        let spelling = match self {
            Self::Equal => "==",
            Self::NotEqual => "!=",
            Self::LessThan => "<",
            Self::LessEqual => "<=",
            Self::GreaterThan => ">",
            Self::GreaterEqual => ">=",
        };
        formatter.write_str(spelling)
    }
}

/// A `.click` `by` clause proving one theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
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
    pub(crate) prerequisite_derivations: Vec<PropositionDerivation>,
    /// Whether this transition's execution can consult the ambient conditions.
    ///
    /// Planning reasons from the whole ambient context, and a condition it used
    /// leaves no trace in the transition, so a certificate for such a statement
    /// has to carry the ambient conditions for replay to reach the same
    /// transition. A statement that only moves a variable or a constant never
    /// asks, and its certificate carries none of them.
    pub(crate) consults_conditions: bool,
    pub(crate) fact_transports: Vec<CertifiedFactTransport>,
}

#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedFactTransport {
    pub(crate) source: Proposition,
    pub(crate) target: Proposition,
    pub(crate) theorem: Theorem,
    pub(crate) statement_local: bool,
}

#[doc(hidden)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedStatementReplay {
    pub(crate) transition: CertifiedStatementTransition,
    pub(crate) next_opaque_call: u64,
    pub(crate) next_verification_variable: u64,
}

/// A tactic in an explicit `.click` proof script.
///
/// Tactics are classified by [`ProofTactic::class`]. A `Proof::Script`
/// certificate is not considered fully expanded while it contains a smart
/// tactic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofTactic {
    Mark(String),
    Step,
    StepUsing(Vec<ClickProposition>),
    CertifiedStatementStep {
        prerequisite_derivations: Vec<PropositionDerivation>,
        exact_premises: Vec<Proposition>,
    },
    CertifiedLoopSummaryStep {
        prerequisite_derivations: Vec<PropositionDerivation>,
        exact_premises: Vec<Proposition>,
    },
    CertifiedStatementReplay(Box<CertifiedStatementReplay>),
    CertifiedLoopSummaryReplay(Box<CertifiedStatementReplay>),
    SmartStep,
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
    If(ProofIf),
    Branch(ProofBranch),
    Loop(StructuralClause),
    ObserveResource(ResourceClause),
    Witness(ProofWitness),
    Choose(ProofChoice),
    Assumption,
    Normalize,
    Intro,
    Split,
    Left,
    Right,
    Contradiction(ClickProposition),
    Derive(ProofDerive),
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
    ExactPropositionDerivation(PropositionDerivation),
    CertifiedFactTransport {
        source: Proposition,
        target: Proposition,
        theorem: Theorem,
    },
    FinishCertifiedFactTransports(Vec<Proposition>),
    CertifiedPathAssumption {
        occurrence: usize,
        condition: ClickProposition,
        value: bool,
        facts: Vec<Proposition>,
        theorem: Theorem,
    },
    CertifiedFrame(Vec<Vec<PropositionDerivation>>),
    CertifiedAlternatives(Vec<ProofReplayPlan>),
    Simp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SimpleTactic {
    Mark,
    StatementTransition,
    CertifiedStatementTransition,
    CertifiedLoopSummaryTransition,
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
    Normalize,
    Intro,
    Split,
    Left,
    Right,
    Contradiction,
    Derive,
    CloseInvariants,
    Rewrite,
    FactTransport,
    ExactPropositionDerivation,
    CertifiedFactTransport,
    CertifiedFactTransportFinish,
    CertifiedPathAssumption,
    CertifiedFrame,
    FoldResource,
    Frame,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SmartTacticKind {
    Auto,
    ApplyTheorem,
    FactTransport,
    SmartStep,
    SmartExecute,
    ExecuteUntil,
    Frame,
    Simp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlFlowTactic {
    Have,
    If,
    Branch,
    Loop,
    CertifiedAlternatives,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TacticClass {
    Simple(SimpleTactic),
    Smart(SmartTacticKind),
    ControlFlow(ControlFlowTactic),
}

/// A validated proof artifact containing no smart tactics.
///
/// Control-flow tactics remain in the existing proof AST, but validation walks
/// every nested proof scope. Constructing a certificate therefore establishes
/// that replay reaches only simple tactics and control flow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TacticCertificate {
    tactics: Vec<ProofTactic>,
}

/// Internal evidence selected by a smart tactic before it is lowered to a
/// surface-expressible [`TacticCertificate`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofReplayPlan {
    tactics: Vec<ProofTactic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertificatePathSegment {
    Tactic(usize),
    HaveBody,
    ThenBranch,
    ElseBranch,
    LoopInitialize,
    LoopPreserve,
    LoopItem(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertificateError {
    tactic_class: TacticClass,
    path: Vec<CertificatePathSegment>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ReplayPlanError {
    smart_tactic: SmartTacticKind,
    path: Vec<CertificatePathSegment>,
}

impl ReplayPlanError {
    fn smart_tactic(&self) -> SmartTacticKind {
        self.smart_tactic
    }
}

impl TacticCertificate {
    pub fn from_proof_tactics(tactics: &[ProofTactic]) -> Result<Self, CertificateError> {
        validate_certificate_tactics(tactics, &mut Vec::new())?;
        Ok(Self {
            tactics: tactics.to_vec(),
        })
    }

    pub fn tactics(&self) -> &[ProofTactic] {
        &self.tactics
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

impl ProofReplayPlan {
    fn from_planned_tactics(tactics: &[ProofTactic]) -> Result<Self, ReplayPlanError> {
        validate_replay_plan_tactics(tactics, &mut Vec::new())?;
        Ok(Self {
            tactics: tactics.to_vec(),
        })
    }

    fn tactics(&self) -> &[ProofTactic] {
        &self.tactics
    }
}

fn validate_certificate_tactics(
    tactics: &[ProofTactic],
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    for (index, tactic) in tactics.iter().enumerate() {
        path.push(CertificatePathSegment::Tactic(index));
        let result = match tactic.class() {
            TacticClass::Simple(simple) if simple.is_surface_expressible() => Ok(()),
            tactic_class @ (TacticClass::Simple(_) | TacticClass::Smart(_)) => {
                Err(CertificateError {
                    tactic_class,
                    path: path.clone(),
                })
            }
            TacticClass::ControlFlow(ControlFlowTactic::CertifiedAlternatives) => {
                Err(CertificateError {
                    tactic_class: tactic.class(),
                    path: path.clone(),
                })
            }
            TacticClass::ControlFlow(ControlFlowTactic::Have) => {
                let ProofTactic::Have(proof_have) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::HaveBody);
                let result = validate_certificate_proof(&proof_have.proof, path);
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

fn validate_replay_plan_tactics(
    tactics: &[ProofTactic],
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), ReplayPlanError> {
    for (index, tactic) in tactics.iter().enumerate() {
        path.push(CertificatePathSegment::Tactic(index));
        let result = match tactic.class() {
            TacticClass::Simple(_) => Ok(()),
            TacticClass::Smart(smart_tactic) => Err(ReplayPlanError {
                smart_tactic,
                path: path.clone(),
            }),
            TacticClass::ControlFlow(ControlFlowTactic::Have) => {
                let ProofTactic::Have(proof_have) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::HaveBody);
                let result = validate_replay_plan_proof(&proof_have.proof, path);
                path.pop();
                result
            }
            TacticClass::ControlFlow(ControlFlowTactic::If) => {
                let ProofTactic::If(proof_if) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::ThenBranch);
                let then_result = validate_replay_plan_tactics(&proof_if.then_tactics, path);
                path.pop();
                if then_result.is_err() {
                    then_result
                } else {
                    path.push(CertificatePathSegment::ElseBranch);
                    let else_result = validate_replay_plan_tactics(&proof_if.else_tactics, path);
                    path.pop();
                    else_result
                }
            }
            TacticClass::ControlFlow(ControlFlowTactic::Branch) => {
                let ProofTactic::Branch(proof_branch) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::ThenBranch);
                let then_result = validate_replay_plan_tactics(&proof_branch.then_tactics, path);
                path.pop();
                if then_result.is_err() {
                    then_result
                } else {
                    path.push(CertificatePathSegment::ElseBranch);
                    let else_result =
                        validate_replay_plan_tactics(&proof_branch.else_tactics, path);
                    path.pop();
                    else_result
                }
            }
            TacticClass::ControlFlow(ControlFlowTactic::Loop) => {
                let ProofTactic::Loop(loop_clause) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::LoopInitialize);
                match loop_clause.initialize_proof() {
                    Some(proof) => validate_replay_plan_proof(proof, path)?,
                    None => {
                        return Err(ReplayPlanError {
                            smart_tactic: SmartTacticKind::Auto,
                            path: path.clone(),
                        });
                    }
                }
                path.pop();
                path.push(CertificatePathSegment::LoopPreserve);
                match loop_clause.preserve_proof() {
                    Some(proof) => validate_replay_plan_proof(proof, path)?,
                    None => {
                        return Err(ReplayPlanError {
                            smart_tactic: SmartTacticKind::Auto,
                            path: path.clone(),
                        });
                    }
                }
                path.pop();
                for (item_index, item) in loop_clause.items().iter().enumerate() {
                    if !item.is_effect_kind() {
                        continue;
                    }
                    path.push(CertificatePathSegment::LoopItem(item_index));
                    validate_replay_plan_proof(item.proof(), path)?;
                    path.pop();
                }
                Ok(())
            }
            TacticClass::ControlFlow(ControlFlowTactic::CertifiedAlternatives) => {
                let ProofTactic::CertifiedAlternatives(alternatives) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                for alternative in alternatives {
                    validate_replay_plan_tactics(alternative.tactics(), path)?;
                }
                Ok(())
            }
        };
        path.pop();
        result?;
    }
    Ok(())
}

fn validate_replay_plan_proof(
    proof: &Proof,
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), ReplayPlanError> {
    match proof {
        Proof::Default => Err(ReplayPlanError {
            smart_tactic: SmartTacticKind::Auto,
            path: path.clone(),
        }),
        Proof::Tactic(smart_tactic) => Err(ReplayPlanError {
            smart_tactic: smart_tactic.kind(),
            path: path.clone(),
        }),
        Proof::Script(tactics) => validate_replay_plan_tactics(tactics, path),
    }
}

fn validate_certificate_proof(
    proof: &Proof,
    path: &mut Vec<CertificatePathSegment>,
) -> Result<(), CertificateError> {
    match proof {
        Proof::Default => Err(CertificateError {
            tactic_class: TacticClass::Smart(SmartTacticKind::Auto),
            path: path.clone(),
        }),
        Proof::Tactic(smart_tactic) => Err(CertificateError {
            tactic_class: TacticClass::Smart(smart_tactic.kind()),
            path: path.clone(),
        }),
        Proof::Script(tactics) => validate_certificate_tactics(tactics, path),
    }
}

impl SimpleTactic {
    fn is_surface_expressible(self) -> bool {
        !matches!(
            self,
            Self::CertifiedStatementTransition
                | Self::CertifiedLoopSummaryTransition
                | Self::ExactPropositionDerivation
                | Self::CertifiedFactTransport
                | Self::CertifiedFactTransportFinish
                | Self::CertifiedPathAssumption
                | Self::CertifiedFrame
        )
    }
}

impl ProofTactic {
    pub fn class(&self) -> TacticClass {
        match self {
            Self::Mark(_) => TacticClass::Simple(SimpleTactic::Mark),
            Self::Step => TacticClass::Simple(SimpleTactic::StatementTransition),
            Self::StepUsing(_) => TacticClass::Simple(SimpleTactic::StatementTransition),
            Self::CertifiedStatementStep { .. } => {
                TacticClass::Simple(SimpleTactic::CertifiedStatementTransition)
            }
            Self::CertifiedStatementReplay(_) => {
                TacticClass::Simple(SimpleTactic::CertifiedStatementTransition)
            }
            Self::CertifiedLoopSummaryReplay(_) => {
                TacticClass::Simple(SimpleTactic::CertifiedLoopSummaryTransition)
            }
            Self::CertifiedLoopSummaryStep { .. } => {
                TacticClass::Simple(SimpleTactic::CertifiedLoopSummaryTransition)
            }
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
            Self::Normalize => TacticClass::Simple(SimpleTactic::Normalize),
            Self::Intro => TacticClass::Simple(SimpleTactic::Intro),
            Self::Split => TacticClass::Simple(SimpleTactic::Split),
            Self::Left => TacticClass::Simple(SimpleTactic::Left),
            Self::Right => TacticClass::Simple(SimpleTactic::Right),
            Self::Contradiction(_) => TacticClass::Simple(SimpleTactic::Contradiction),
            Self::Derive(_) => TacticClass::Simple(SimpleTactic::Derive),
            Self::CloseInvariants => TacticClass::Simple(SimpleTactic::CloseInvariants),
            Self::Rewrite(_) => TacticClass::Simple(SimpleTactic::Rewrite),
            Self::Transport { .. } => TacticClass::Smart(SmartTacticKind::FactTransport),
            Self::TransportUsing { .. } => TacticClass::Simple(SimpleTactic::FactTransport),
            Self::ExactPropositionDerivation(_) => {
                TacticClass::Simple(SimpleTactic::ExactPropositionDerivation)
            }
            Self::CertifiedFactTransport { .. } => {
                TacticClass::Simple(SimpleTactic::CertifiedFactTransport)
            }
            Self::FinishCertifiedFactTransports(_) => {
                TacticClass::Simple(SimpleTactic::CertifiedFactTransportFinish)
            }
            Self::CertifiedPathAssumption { .. } => {
                TacticClass::Simple(SimpleTactic::CertifiedPathAssumption)
            }
            Self::CertifiedFrame(_) => TacticClass::Simple(SimpleTactic::CertifiedFrame),
            Self::FoldResource(_) => TacticClass::Simple(SimpleTactic::FoldResource),
            Self::FrameUsing { .. } => TacticClass::Simple(SimpleTactic::Frame),
            Self::SmartStep => TacticClass::Smart(SmartTacticKind::SmartStep),
            Self::SmartExecute | Self::SmartExecuteAllPaths => {
                TacticClass::Smart(SmartTacticKind::SmartExecute)
            }
            Self::ExecuteUntil(_) => TacticClass::Smart(SmartTacticKind::ExecuteUntil),
            Self::SmartFrame(_) => TacticClass::Smart(SmartTacticKind::Frame),
            Self::Simp => TacticClass::Smart(SmartTacticKind::Simp),
            Self::Have(_) => TacticClass::ControlFlow(ControlFlowTactic::Have),
            Self::If(_) => TacticClass::ControlFlow(ControlFlowTactic::If),
            Self::Branch(_) => TacticClass::ControlFlow(ControlFlowTactic::Branch),
            Self::Loop(_) => TacticClass::ControlFlow(ControlFlowTactic::Loop),
            Self::CertifiedAlternatives(_) => {
                TacticClass::ControlFlow(ControlFlowTactic::CertifiedAlternatives)
            }
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
    proof: Proof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofIf {
    condition: ClickProposition,
    then_tactics: Vec<ProofTactic>,
    else_tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofBranch {
    ensuring: Option<Vec<ProofAssertion>>,
    then_tactics: Vec<ProofTactic>,
    else_tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofDerive {
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
    #[doc(hidden)]
    Mark(String),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum VisitSelector {
    ProgramPoint(ProgramPointRef),
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
    pub expanded_proof_tactics: Option<Vec<ProofTactic>>,
    pub expansion_blocker: Option<String>,
    pub specification: CFunctionSpecification,
    pub theorem: Theorem,
    pub concrete_loop_execution: bool,
    pub(crate) frontier_loop_clauses: Vec<StructuralClause>,
    pub(crate) frontier_loop_rules: Vec<CVerifiedLoopRule>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedPureTheorem {
    pub theorem_definition: TheoremDefinition,
    pub ensure_index: usize,
    pub ensure_clause: EnsureClause,
    pub proof_kind: ProofKind,
    pub proof_tactics: Option<Vec<ProofTactic>>,
    pub requires: Vec<Proposition>,
    pub conclusion: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VerifiedClaim {
    Ensure { index: usize, clause: EnsureClause },
    Effect { index: usize, clause: EffectClause },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofKind {
    Pure,
    Frame,
    Simp,
    TacticScript,
    LoopVerification,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClickError {
    message: String,
    /// Internal marker for the selected-tactic expansion capture: when a
    /// probe records its expansion, verification is aborted with an error
    /// carrying this flag instead of a real failure. Control flow must test
    /// this flag, never the message text.
    expansion_complete: bool,
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

    pub fn multiplicity(&self) -> ResourceMultiplicity {
        self.multiplicity
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

    pub fn grouped_proof(&self) -> Option<&Proof> {
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

    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl EffectClause {
    pub fn effect(&self) -> &Effect {
        &self.effect
    }

    pub fn proof(&self) -> &Proof {
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

    pub fn initialize_proof(&self) -> Option<&Proof> {
        self.initialize_proof.as_ref()
    }

    pub fn preserve_proof(&self) -> Option<&Proof> {
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

    pub fn proof(&self) -> &Proof {
        &self.proof
    }
}

impl Proof {
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
            Self::Script(tactics) => tactics
                .iter()
                .filter_map(|tactic| match tactic {
                    ProofTactic::UnfoldPredicate(name) => Some(name.clone()),
                    _ => None,
                })
                .collect(),
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

impl VerifiedCTheorem {
    pub fn proof_kind(&self) -> ProofKind {
        self.proof_kind
    }

    pub fn proof_tactics(&self) -> Option<&[ProofTactic]> {
        self.proof_tactics.as_deref()
    }

    pub fn expanded_proof_tactics(&self) -> Option<&[ProofTactic]> {
        self.expanded_proof_tactics.as_deref()
    }

    pub fn expansion_blocker(&self) -> Option<&str> {
        self.expansion_blocker.as_deref()
    }

    pub fn expanded_proof_certificate(&self) -> Result<TacticCertificate, ClickError> {
        let tactics = self.expanded_proof_tactics.as_deref().ok_or_else(|| {
            ClickError::new(format!(
                "proof expansion is unavailable for `{}`: {}",
                self.function_block.signature().name(),
                self.expansion_blocker
                    .as_deref()
                    .unwrap_or("verification did not record a surface expansion")
            ))
        })?;
        TacticCertificate::from_proof_tactics(tactics).map_err(|error| {
            ClickError::new(format!(
                "recorded proof expansion for `{}` is not a surface certificate: {error:?}",
                self.function_block.signature().name()
            ))
        })
    }

    pub fn expanded_proof_source(&self) -> Result<String, ClickError> {
        Ok(format_tactic_certificate(
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
    pub fn proof_certificate(&self) -> Result<TacticCertificate, ClickError> {
        let tactics = self.proof_tactics.as_deref().ok_or_else(|| {
            ClickError::new(format!(
                "pure theorem `{}` ensure {} has no surface certificate",
                self.theorem_definition.name(),
                self.ensure_index
            ))
        })?;
        TacticCertificate::from_proof_tactics(tactics).map_err(|error| {
            ClickError::new(format!(
                "pure theorem `{}` ensure {} recorded an invalid surface certificate: {error:?}",
                self.theorem_definition.name(),
                self.ensure_index
            ))
        })
    }

    pub fn expanded_proof_source(&self) -> Result<String, ClickError> {
        Ok(format_tactic_certificate(&self.proof_certificate()?))
    }
}

impl ClickError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: diagnostics::bound_error_message(message.into()),
            expansion_complete: false,
            timing_tactic: current_timing_tactic(),
        }
    }

    /// The internal sentinel that unwinds verification once a selected-tactic
    /// expansion has been captured; see `proof::capture_c0_tactic_expansion`.
    pub(crate) fn expansion_complete() -> Self {
        Self {
            message: "internal: selected tactic expansion complete".into(),
            expansion_complete: true,
            timing_tactic: None,
        }
    }

    pub(crate) fn is_expansion_complete(&self) -> bool {
        self.expansion_complete
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    fn emit_timing_failure(&self) {
        if !instrumentation::enabled() || self.expansion_complete {
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
