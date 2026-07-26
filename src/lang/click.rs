//! Tiny `.click` sidecar verifier for the C0 kernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::kernel::{
    Assumptions, Bitvector32Term, CComparisonOperator, CConditionOutcome, CExecutionEnvironment,
    CExecutionSemantics, CExpression, CExpressionOutcome, CFunction, CFunctionContractClaim,
    CFunctionContractClaimKey, CFunctionOutcome, CFunctionSpecification, CLoopEffect,
    CLoopEffectCheck, CLoopEffectSpan, CLoopInvariantCheck, CMemory, CMemoryRange, CMemorySegment,
    CResource, CResourceAccessMode, CResourceFact, CResourceSpec, CState, CStatement,
    CStatementOutcome, CType, CValue, CVerifiedLoopRule, ConditionTerm, ExecutionBudget,
    ExecutionPureFact, Pointer, PointerOffsetTerm, ProofObligation, Proposition,
    PropositionDerivation, ResourceContext, ResourceContextValidityError, Sort, SpecExpression,
    SpecMemory, SpecPredicateArgument, SpecProposition, SpecResource, SymbolicCExecution, Term,
    Theorem, Variable, abstract_c_state_for_join, c_condition_fact_has_memory,
    c_condition_fact_memories, c_expression_definedness_proposition, c_function,
    c_function_entry_state, c_function_outcome_from_statement_outcome, c_function_specification,
    c_if, c_labeled_assert, c_loop_effects_hold_at_back_edge,
    c_loop_invariant_obligations_at_entry, c_loop_invariants_hold_at_back_edge_using,
    c_loop_invariants_hold_at_entry, c_loop_preservation_contexts,
    c_pointer_offsets_proven_equal_for_effect, c_pointer_value, c_resources_directly_match, c_seq,
    c_verified_function_contract_claim, c_verified_function_rule,
    c_while_with_invariant_and_effect_checks, canonical_c_memory_for_pointer_load,
    certify_c_function_execution_paths_from_outcomes, int32,
    prove_c_condition_fact_direct_transport, prove_c_condition_fact_transport,
    prove_c_function_satisfies_specification_from_symbolic_path,
    prove_symbolic_c_condition_evaluation,
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
use checking::*;
pub use expansion::{
    CProofClaim, SourcePosition, c0_tactic_source_position, expand_c0_claim_source,
    expand_c0_tactic_source_at, verifying_source_paths,
};
use expansion::ProofSite;
use lowering::*;
use parser::ContractLetBinding;
pub use printing::{format_proof_tactics, format_tactic_certificate};
use proof::*;
use validation::{
    combined_click_function_definitions, combined_predicate_definitions,
    combined_resource_definitions, combined_theorem_definitions,
    combined_theorem_definitions_with_stdlib_ensure_count, contains_at_expression,
    contains_old_expression, describe_c0_type, describe_resource_clause,
};

const EXTERNAL_ARGUMENT_MEMORY_BLOCK: &str = "arg-memory";
const POINTER_ARGUMENT_VARIABLE_BASE: u64 = 100_000;
const MAX_CONCRETE_RANGE_FOLD_STEPS: i64 = 1024;

const CLICK_STANDARD_LIBRARY: &str = include_str!("../../stdlib/prelude.click");

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
    structural_clauses: Vec<StructuralClause>,
    effects: Vec<EffectClause>,
    ensures: Vec<EnsureClause>,
    grouped_proof: Option<Proof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSignature {
    return_type: C0Type,
    name: String,
    parameters: Vec<FunctionParameter>,
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
    LoadableBytes {
        name: String,
        bytes: RangeBytes,
    },
    LoadableSegment {
        segment: ContractSegment,
    },
    Resource(ResourceClause),
    Proposition(ClickProposition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RangeBytes {
    Constant(u32),
    Parameter(String),
    Add(Box<RangeBytes>, Box<RangeBytes>),
    Subtract(Box<RangeBytes>, Box<RangeBytes>),
    Multiply(Box<RangeBytes>, Box<RangeBytes>),
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
    Assert,
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
            (ClickProposition::Not(_), Proposition::ConditionIs(_, false)) => Ok(()),
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
    Step,
    StepUsing(Vec<ClickProposition>),
    ApplyLoopSummary(CodeRegionRef),
    ApplyLoopSummaryUsing {
        region: CodeRegionRef,
        premises: Vec<ClickProposition>,
    },
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
    ExecuteStep,
    ExecuteThenStep,
    ExecuteElseStep,
    ExecuteRest,
    ExecuteUntil(CodeRegionRef),
    BoundedExecute,
    ContextualFrame,
    Frame(Option<CodeRegionRef>),
    UnfoldPredicate(String),
    UnfoldResource(ResourceClause),
    FoldResource(ResourceClause),
    ApplyTheorem(TheoremApplication),
    ApplyTheoremUsing {
        application: TheoremApplication,
        premises: Vec<ClickProposition>,
    },
    Have(ProofHave),
    If(ProofIf),
    Advance(ProofAdvance),
    ObserveResource(ResourceClause),
    Witness(ProofWitness),
    Choose(ProofChoice),
    Assumption,
    Normalize,
    Intro,
    Conjunction,
    Left,
    Right,
    DoubleNegation,
    Vacuous,
    Contradiction(ClickProposition),
    Derive(ProofDerive),
    Calculate(ProofDerive),
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
    StatementTransition,
    LoopSummaryTransition,
    CertifiedStatementTransition,
    CertifiedLoopSummaryTransition,
    UnfoldPredicate,
    UnfoldResource,
    ObserveResource,
    ApplyTheorem,
    Witness,
    Choose,
    Assumption,
    Normalize,
    Intro,
    Conjunction,
    Left,
    Right,
    DoubleNegation,
    Vacuous,
    Contradiction,
    Derive,
    Calculate,
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
    ExecuteStep,
    ExecuteThenStep,
    ExecuteElseStep,
    ExecuteRest,
    ExecuteUntil,
    BoundedExecute,
    Frame,
    Simp,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ControlFlowTactic {
    Have,
    If,
    Advance,
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
    AdvanceBody,
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
            TacticClass::ControlFlow(ControlFlowTactic::Advance) => {
                let ProofTactic::Advance(proof_advance) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::AdvanceBody);
                let result = validate_certificate_tactics(&proof_advance.tactics, path);
                path.pop();
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
            TacticClass::ControlFlow(ControlFlowTactic::Advance) => {
                let ProofTactic::Advance(proof_advance) = tactic else {
                    unreachable!("tactic class and variant must agree")
                };
                path.push(CertificatePathSegment::AdvanceBody);
                let result = validate_replay_plan_tactics(&proof_advance.tactics, path);
                path.pop();
                result
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
            Self::Step => TacticClass::Simple(SimpleTactic::StatementTransition),
            Self::StepUsing(_) => TacticClass::Simple(SimpleTactic::StatementTransition),
            Self::ApplyLoopSummary(_) | Self::ApplyLoopSummaryUsing { .. } => {
                TacticClass::Simple(SimpleTactic::LoopSummaryTransition)
            }
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
            Self::ApplyTheorem(_) => TacticClass::Smart(SmartTacticKind::ApplyTheorem),
            Self::ApplyTheoremUsing { .. } => TacticClass::Simple(SimpleTactic::ApplyTheorem),
            Self::Witness(_) => TacticClass::Simple(SimpleTactic::Witness),
            Self::Choose(_) => TacticClass::Simple(SimpleTactic::Choose),
            Self::Assumption => TacticClass::Simple(SimpleTactic::Assumption),
            Self::Normalize => TacticClass::Simple(SimpleTactic::Normalize),
            Self::Intro => TacticClass::Simple(SimpleTactic::Intro),
            Self::Conjunction => TacticClass::Simple(SimpleTactic::Conjunction),
            Self::Left => TacticClass::Simple(SimpleTactic::Left),
            Self::Right => TacticClass::Simple(SimpleTactic::Right),
            Self::DoubleNegation => TacticClass::Simple(SimpleTactic::DoubleNegation),
            Self::Vacuous => TacticClass::Simple(SimpleTactic::Vacuous),
            Self::Contradiction(_) => TacticClass::Simple(SimpleTactic::Contradiction),
            Self::Derive(_) => TacticClass::Simple(SimpleTactic::Derive),
            Self::Calculate(_) => TacticClass::Simple(SimpleTactic::Calculate),
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
            Self::Frame(_) => TacticClass::Simple(SimpleTactic::Frame),
            Self::ExecuteStep => TacticClass::Smart(SmartTacticKind::ExecuteStep),
            Self::ExecuteThenStep => TacticClass::Smart(SmartTacticKind::ExecuteThenStep),
            Self::ExecuteElseStep => TacticClass::Smart(SmartTacticKind::ExecuteElseStep),
            Self::ExecuteRest => TacticClass::Smart(SmartTacticKind::ExecuteRest),
            Self::ExecuteUntil(_) => TacticClass::Smart(SmartTacticKind::ExecuteUntil),
            Self::BoundedExecute => TacticClass::Smart(SmartTacticKind::BoundedExecute),
            Self::ContextualFrame => TacticClass::Smart(SmartTacticKind::Frame),
            Self::Simp => TacticClass::Smart(SmartTacticKind::Simp),
            Self::Have(_) => TacticClass::ControlFlow(ControlFlowTactic::Have),
            Self::If(_) => TacticClass::ControlFlow(ControlFlowTactic::If),
            Self::Advance(_) => TacticClass::ControlFlow(ControlFlowTactic::Advance),
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
pub struct ProofAdvance {
    target: ProgramPointRef,
    assertions: Vec<ProofAssertion>,
    tactics: Vec<ProofTactic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofDerive {
    proposition: ClickProposition,
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
struct ResourceEnvironment {
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
}

impl FunctionSignature {
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
        C0Type::Int32 | C0Type::UInt8 => None,
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

    pub fn items(&self) -> &[StructuralItem] {
        &self.items
    }

    pub fn initialize_proof(&self) -> Option<&Proof> {
        self.initialize_proof.as_ref()
    }

    pub fn preserve_proof(&self) -> Option<&Proof> {
        self.preserve_proof.as_ref()
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
            message: message.into(),
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

pub fn parse(source: &str) -> Result<ClickFile, ClickError> {
    parser::parse(source)
}

pub fn verify_click_theorems(click_source: &str) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let file = parse(click_source)?;
    verify_click_file_theorems(&file)
}

fn verify_click_file_theorems(file: &ClickFile) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let predicate_definitions = combined_predicate_definitions(&file)?;
    let click_function_definitions = combined_click_function_definitions(&file)?;
    let (theorem_definitions, stdlib_theorem_ensure_count) =
        combined_theorem_definitions_with_stdlib_ensure_count(&file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);
    let verified = verify_theorem_definitions(
        &theorem_definitions,
        &predicate_environment,
        &click_function_environment,
    )?;
    Ok(verified
        .into_iter()
        .skip(stdlib_theorem_ensure_count)
        .collect())
}

fn verify_click_theorems_with_c_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let layouts = parse_c_struct_layouts(&sources)?;
    let file = parser::parse_with_struct_layouts(click_source, layouts)?;
    verify_click_file_theorems(&file)
}

pub fn verify_c0_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let c_sources: BTreeMap<&str, &str> = c_sources.iter().copied().collect();
    let struct_layouts = parse_c_struct_layouts(&c_sources)?;
    let file = parser::parse_with_struct_layouts(click_source, struct_layouts)?;
    let parsed_sources = parse_verified_sources(&file, &c_sources)?;
    let tactic_expansion_functions = proof::active_c0_tactic_expansion_request()
        .map(|request| tactic_expansion_required_functions(&file, &parsed_sources, request))
        .transpose()?;
    let predicate_definitions = combined_predicate_definitions(&file)?;
    let click_function_definitions = combined_click_function_definitions(&file)?;
    let resource_definitions = combined_resource_definitions(&file)?;
    let theorem_definitions = combined_theorem_definitions(&file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);
    let resource_environment = ResourceEnvironment::new(&resource_definitions);
    let mut function_environment = build_function_environment(
        &parsed_sources,
        file.function_blocks(),
        &predicate_environment,
        &click_function_environment,
        &resource_environment,
    )?;
    let _verified_theorems = verify_theorem_definitions(
        &theorem_definitions,
        &predicate_environment,
        &click_function_environment,
    )?;
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let mut verified = Vec::new();

    for function_block in file.function_blocks {
        if tactic_expansion_functions
            .as_ref()
            .is_some_and(|functions| !functions.contains(function_block.signature.name()))
        {
            continue;
        }
        let function_timing_start = std::time::Instant::now();
        let (source_path, parsed_function) = parsed_sources
            .get(function_block.signature.name())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{}` is not defined by any `verifying` source",
                    function_block.signature.name()
                ))
            })?;
        check_signature(&function_block.signature, parsed_function, source_path)?;
        validate_region_proof_clauses(&function_block, parsed_function)?;
        let verified_loop_rules = verify_loop_execution_proofs(
            &function_block,
            parsed_function,
            &function_environment,
            &predicate_environment,
            &click_function_environment,
            &resource_environment,
            &theorem_environment,
        )?;
        let verification_function_environment = function_environment
            .clone()
            .with_verified_loop_rules(verified_loop_rules);
        let implicit_safety_clause = EnsureClause {
            name: None,
            ensure: Ensure::Proposition(ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Value(int32(0))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(0))),
            }),
            proof: Proof::Tactic(SmartTactic::Auto),
        };
        let mut claims = function_claims(&function_block);
        let has_explicit_claims = !claims.is_empty();
        if !has_explicit_claims {
            claims.push(FunctionClaimRef::Ensure(0, &implicit_safety_clause));
        }
        let mut function_verified = Vec::new();
        if let Some(grouped_proof) = function_block.grouped_proof() {
            if !has_explicit_claims {
                return Err(ClickError::new(format!(
                    "grouped proof for `{}` requires at least one effect or postcondition",
                    function_block.signature().name()
                )));
            }
            let theorems = match grouped_proof {
                Proof::Tactic(SmartTactic::Auto) => prove_claims_by_grouped_auto(
                    source_path,
                    &function_block,
                    parsed_function,
                    &claims,
                    &verification_function_environment,
                    &predicate_environment,
                    &click_function_environment,
                    &resource_environment,
                    &theorem_environment,
                )?,
                Proof::Script(tactics) => prove_claims_by_grouped_tactics(
                    source_path,
                    &function_block,
                    parsed_function,
                    &claims,
                    &verification_function_environment,
                    &predicate_environment,
                    &click_function_environment,
                    &resource_environment,
                    &theorem_environment,
                    tactics,
                )?,
                Proof::Default | Proof::Tactic(SmartTactic::Simp | SmartTactic::Frame) => {
                    return Err(ClickError::new(format!(
                        "grouped proof for `{}` must use `by auto;` or an explicit `by {{ ... }}` proof script",
                        function_block.signature().name()
                    )));
                }
            };
            function_verified.extend(theorems.iter().cloned());
            verified.extend(theorems);
        } else {
            for claim in claims {
                let claim_label = if has_explicit_claims {
                    function_claim_label(function_block.signature.name(), &claim)
                } else {
                    format!("{}.body_safety", function_block.signature.name())
                };
                let theorems = match claim.proof() {
                    Proof::Default | Proof::Tactic(SmartTactic::Auto) => prove_claim_by_auto(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?,
                    Proof::Tactic(SmartTactic::Frame) => prove_claim_by_frame(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?,
                    Proof::Tactic(SmartTactic::Simp) => prove_claim_by_simp(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?,
                    Proof::Script(tactics) => prove_claim_by_tactics(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                        tactics,
                    )?,
                };
                function_verified.extend(theorems.iter().cloned());
                if has_explicit_claims {
                    verified.extend(theorems);
                }
            }
        }
        let contract_function = function_environment
            .get_function(function_block.signature.name())
            .cloned()
            .expect("verified source should be present in the function environment");
        let proof_objects = function_verified
            .iter()
            .map(|verified| {
                let key = if has_explicit_claims {
                    match &verified.claim {
                        VerifiedClaim::Ensure { index, .. } => {
                            CFunctionContractClaimKey::Ensure(*index)
                        }
                        VerifiedClaim::Effect { index, .. } => {
                            CFunctionContractClaimKey::Effect(*index)
                        }
                    }
                } else {
                    CFunctionContractClaimKey::BodySafety
                };
                c_verified_function_contract_claim(&contract_function, key, &verified.theorem)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "could not certify a contract claim for `{}`",
                            function_block.signature.name()
                        ))
                    })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if contract_function.opaque_contract_supported() {
            let rule =
                c_verified_function_rule(contract_function, &proof_objects).ok_or_else(|| {
                    ClickError::new(format!(
                        "could not package verified contract for `{}`",
                        function_block.signature.name()
                    ))
                })?;
            function_environment = function_environment.with_verified_function_rule(rule);
        }
        if std::env::var_os("CLICK_TIMINGS").is_some() {
            eprintln!(
                "click timing: function {} {:.3}s",
                function_block.signature.name(),
                function_timing_start.elapsed().as_secs_f64()
            );
        }
    }

    Ok(verified)
}

fn tactic_expansion_required_functions(
    file: &ClickFile,
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    (site, tactic_index): (ProofSite, Option<usize>),
) -> Result<BTreeSet<String>, ClickError> {
    let ProofSite::FunctionClaim {
        function_name,
        claim,
    } = site
    else {
        return Ok(file
            .function_blocks()
            .iter()
            .map(|function| function.signature().name().to_string())
            .collect());
    };
    let tactic_index = tactic_index.ok_or_else(|| {
        ClickError::new(format!(
            "whole-proof capture is not supported for function claim {claim:?}"
        ))
    })?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let tactics = match claim {
        CProofClaim::Grouped => function_block.grouped_proof().and_then(Proof::tactics),
        CProofClaim::Ensure(index) => function_block
            .ensures()
            .get(index)
            .and_then(|clause| clause.proof().tactics()),
        CProofClaim::Effect(index) => function_block
            .effects()
            .get(index)
            .and_then(|clause| clause.proof().tactics()),
    }
    .ok_or_else(|| {
        ClickError::new(format!(
            "selected {claim:?} proof for `{function_name}` is not an explicit tactic script"
        ))
    })?;
    let parsed_function = &parsed_sources
        .get(&function_name)
        .ok_or_else(|| ClickError::new(format!("no C source defines `{function_name}`")))?
        .1;
    let statement_calls = c0_statement_calls(parsed_function.body());
    let touched_end = proof_statement_prefix_end(tactics, tactic_index, statement_calls.len());
    let mut required = BTreeSet::from([function_name]);
    let mut pending = statement_calls
        .iter()
        .take(touched_end)
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    while let Some(dependency) = pending.pop() {
        if !required.insert(dependency.clone()) {
            continue;
        }
        if let Some((_, parsed)) = parsed_sources.get(&dependency) {
            pending.extend(c0_statement_calls(parsed.body()).into_iter().flatten());
        }
    }
    Ok(required)
}

fn proof_statement_prefix_end(
    tactics: &[ProofTactic],
    selected_tactic: usize,
    statement_count: usize,
) -> usize {
    let mut cursor = 0_usize;
    let Some(prefix) = tactics.get(..=selected_tactic) else {
        return statement_count;
    };
    for tactic in prefix {
        match tactic {
            ProofTactic::Step | ProofTactic::StepUsing(_) | ProofTactic::ExecuteStep => {
                cursor = cursor.saturating_add(1)
            }
            ProofTactic::ExecuteUntil(CodeRegionRef::Statement(target)) => cursor = *target,
            ProofTactic::ExecuteRest | ProofTactic::BoundedExecute => cursor = statement_count,
            ProofTactic::ExecuteThenStep
            | ProofTactic::ExecuteElseStep
            | ProofTactic::If(_)
            | ProofTactic::Advance(_)
            | ProofTactic::ExecuteUntil(CodeRegionRef::Function | CodeRegionRef::Loop(_)) => {
                return statement_count;
            }
            ProofTactic::ExecuteUntil(CodeRegionRef::Label(_)) => return statement_count,
            _ => {}
        }
    }
    cursor.min(statement_count)
}

fn c0_statement_calls(statement: &syntax::C0Statement) -> Vec<BTreeSet<String>> {
    fn visit(statement: &syntax::C0Statement, calls: &mut Vec<BTreeSet<String>>) {
        match statement {
            syntax::C0Statement::Seq(first, second) => {
                visit(first, calls);
                visit(second, calls);
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                calls.push(BTreeSet::new());
                visit(then_branch, calls);
                visit(else_branch, calls);
            }
            syntax::C0Statement::While { body, .. } => {
                calls.push(BTreeSet::new());
                visit(body, calls);
            }
            syntax::C0Statement::CallAssign { function_name, .. } => {
                calls.push(BTreeSet::from([function_name.clone()]));
            }
            syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::Assign { .. }
            | syntax::C0Statement::Return(_)
            | syntax::C0Statement::Store { .. } => calls.push(BTreeSet::new()),
        }
    }

    let mut calls = Vec::new();
    visit(statement, &mut calls);
    calls
}

fn parse_c_struct_layouts(
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, syntax::C0StructLayout>, ClickError> {
    let mut layouts = BTreeMap::new();
    for (source_path, c_source) in c_sources {
        let function = syntax::parse_function(c_source).map_err(|error| {
            ClickError::new(format!(
                "failed to parse C source `{source_path}`: {}",
                error.message()
            ))
        })?;
        for (name, layout) in function.structs() {
            if let Some(previous) = layouts.insert(name.clone(), layout.clone())
                && previous != *layout
            {
                return Err(ClickError::new(format!(
                    "conflicting declarations for struct `{name}`"
                )));
            }
        }
    }
    Ok(layouts)
}

fn parse_verified_sources(
    file: &ClickFile,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, (String, syntax::C0Function)>, ClickError> {
    if file.verifying_sources.is_empty() {
        if file.function_blocks().is_empty() {
            return Ok(BTreeMap::new());
        }
        return Err(ClickError::new(
            "`.click` file must declare at least one `verifying \"source.c\";`",
        ));
    }

    let mut parsed = BTreeMap::new();
    for source_path in &file.verifying_sources {
        let c_source = *c_sources.get(source_path.as_str()).ok_or_else(|| {
            ClickError::new(format!(
                "`verifying` refers to missing C source `{source_path}`"
            ))
        })?;
        let function = syntax::parse_function(c_source).map_err(|error| {
            ClickError::new(format!(
                "failed to parse C source `{source_path}`: {}",
                error.message()
            ))
        })?;
        let function_name = function.name().to_string();
        let previous = parsed.insert(function_name.clone(), (source_path.clone(), function));
        if previous.is_some() {
            return Err(ClickError::new(format!(
                "more than one `verifying` source defines function `{function_name}`"
            )));
        }
    }

    Ok(parsed)
}

fn build_function_environment(
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    function_blocks: &[FunctionBlock],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<CExecutionEnvironment, ClickError> {
    let mut environment = CExecutionEnvironment::new();
    for (_, function) in parsed_sources.values() {
        let function = match function_blocks
            .iter()
            .find(|block| block.signature().name() == function.name())
        {
            Some(function_block) => {
                let (resource_requires, resource_ensures) =
                    function_resource_summary(function_block, resource_environment)?;
                let (
                    contract_requires,
                    contract_ensures,
                    contract_mutable,
                    contract_claims,
                    opaque_supported,
                ) = function_contract_summary(
                    function_block,
                    function,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                )?;
                function
                    .to_kernel_function()
                    .with_resource_summary(resource_requires, resource_ensures)
                    .with_contract(
                        contract_requires,
                        contract_ensures,
                        contract_mutable,
                        contract_claims,
                        opaque_supported,
                    )
            }
            None => function.to_kernel_function(),
        };
        environment = environment.with_function(function);
    }
    Ok(environment)
}

fn function_resource_summary(
    function_block: &FunctionBlock,
    resource_environment: &ResourceEnvironment,
) -> Result<(Vec<CResourceSpec>, Vec<CResourceSpec>), ClickError> {
    let mut requires = Vec::new();
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement.inner() else {
            continue;
        };
        append_entry_resource_specs(resource, resource_environment, &mut requires)?;
    }
    let ensures = function_block
        .ensures()
        .iter()
        .filter_map(|ensure| match ensure.ensure() {
            Ensure::Resource(resource) => Some(resource_clause_to_resource_spec(resource)),
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((requires, ensures))
}

fn append_entry_resource_specs(
    resource: &ResourceClause,
    _resource_environment: &ResourceEnvironment,
    specs: &mut Vec<CResourceSpec>,
) -> Result<(), ClickError> {
    specs.push(resource_clause_to_resource_spec(resource)?);
    Ok(())
}

fn resource_argument_contract_substitutions(
    definition: &ResourceDefinition,
    arguments: &[ContractExpression],
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "resource `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

fn substitute_resource_clause_for_summary(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(substitute_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(substitute_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

fn substitute_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
    })
}

fn resource_clause_to_resource_spec(
    resource: &ResourceClause,
) -> Result<CResourceSpec, ClickError> {
    match resource {
        ResourceClause::Read(segment) => Ok(CResourceSpec::Read(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
        ResourceClause::Write(segment) => Ok(CResourceSpec::Write(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            let access = resource_access_to_kernel(*access);
            let arguments = arguments
                .iter()
                .map(resource_argument_to_c_expression)
                .collect::<Result<Vec<_>, _>>()?;
            let parameter_types = parameter_types
                .iter()
                .map(|c_type| c_type.to_kernel_type())
                .collect();
            Ok(match kind {
                ResourceKind::Composite => CResourceSpec::Composite {
                    access,
                    name: name.clone(),
                    arguments,
                    parameter_types,
                },
                ResourceKind::Token => CResourceSpec::Token {
                    access,
                    name: name.clone(),
                    arguments,
                    parameter_types,
                },
            })
        }
    }
}

fn resource_access_to_kernel(access: ResourceAccessMode) -> CResourceAccessMode {
    match access {
        ResourceAccessMode::Own => CResourceAccessMode::Own,
        ResourceAccessMode::View => CResourceAccessMode::View,
    }
}

fn function_claim_label(function_name: &str, claim: &FunctionClaimRef<'_>) -> String {
    match claim {
        FunctionClaimRef::Ensure(index, ensure) => match ensure.name() {
            Some(name) => format!("{function_name}.{name}"),
            None => format!("{function_name}.ensures_{index}"),
        },
        FunctionClaimRef::Effect(index, effect) => match effect.effect() {
            Effect::Immutable => format!("{function_name}.immutable_{index}"),
            Effect::Mutable(_) => format!("{function_name}.mutable_{index}"),
        },
    }
}

fn implication_body(proposition: &Proposition) -> &Proposition {
    match proposition {
        Proposition::Implies(_, body) => implication_body(body),
        _ => proposition,
    }
}

fn assumptions_from_propositions(propositions: &[Proposition]) -> Assumptions {
    propositions
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition)
}

fn check_signature(
    signature: &FunctionSignature,
    parsed_function: &syntax::C0Function,
    source_path: &str,
) -> Result<(), ClickError> {
    if signature.return_type() != parsed_function.return_type() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click return type is {:?}, C return type is {:?}",
            signature.name(),
            signature.return_type(),
            parsed_function.return_type()
        )));
    }

    if signature.parameters().len() != parsed_function.parameters().len() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click has {} parameters, C has {}",
            signature.name(),
            signature.parameters().len(),
            parsed_function.parameters().len()
        )));
    }

    for (index, (expected, actual)) in signature
        .parameters()
        .iter()
        .zip(parsed_function.parameters())
        .enumerate()
    {
        if expected.c_type() != actual.c_type()
            || expected.name() != actual.name()
            || expected.struct_name() != actual.struct_name()
        {
            return Err(ClickError::new(format!(
                "signature mismatch for `{}` parameter {} in `{source_path}`: .click has {} {}, C has {} {}",
                signature.name(),
                index + 1,
                describe_parameter_type(expected.c_type(), expected.struct_name()),
                expected.name(),
                describe_parameter_type(actual.c_type(), actual.struct_name()),
                actual.name()
            )));
        }
    }

    Ok(())
}

fn describe_parameter_type(c_type: C0Type, struct_name: Option<&str>) -> String {
    match struct_name {
        Some(name) => format!("struct {name}*"),
        None => format!("{c_type:?}"),
    }
}

fn validate_region_proof_clauses(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    let statement_count = count_statements(parsed_function.body());
    for region_proof_clause in function_block.structural_clauses() {
        match region_proof_clause.region() {
            CodeRegion::Function => {
                return Err(ClickError::new(
                    "`for function` region proof blocks are not supported",
                ));
            }
            CodeRegion::Loop(index) if *index >= loop_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `loop({index})` code region; it contains {loop_count} loop(s)",
                    function_block.signature().name()
                )));
            }
            CodeRegion::Statement(index) if *index >= statement_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `statement({index})` code region; it contains {statement_count} statement(s)",
                    function_block.signature().name()
                )));
            }
            CodeRegion::Statement(_) => {
                if region_proof_clause.initialize_proof().is_some()
                    || region_proof_clause.preserve_proof().is_some()
                {
                    return Err(ClickError::new(
                        "`initialize` and `preserve` are only supported at loop code regions",
                    ));
                }
                for item in region_proof_clause.items() {
                    if item.kind() == StructuralItemKind::Invariant {
                        return Err(ClickError::new(
                            "`invariant` is only supported at loop code regions",
                        ));
                    }
                    if item.is_effect_kind() {
                        return Err(ClickError::new(
                            "`immutable` and `mutable` are only supported at loop code regions inside region proof blocks",
                        ));
                    }
                }
            }
            CodeRegion::Loop(_) => {}
        }

        for (phase, proof) in [
            ("initialize", region_proof_clause.initialize_proof()),
            ("preserve", region_proof_clause.preserve_proof()),
        ] {
            let Some(proof) = proof else {
                continue;
            };
            if proof.is_frame_tactic() {
                return Err(ClickError::new(format!(
                    "`{phase}` must use `auto`, `simp`, or an explicit proof script"
                )));
            }
        }

        validate_loop_phase_proof("initialize", region_proof_clause.initialize_proof())?;
        validate_loop_phase_proof("preserve", region_proof_clause.preserve_proof())?;

        for item in region_proof_clause.items() {
            if item.is_effect_kind() {
                if !item.proof().is_auto_or_frame_tactic()
                    && !matches!(
                        item.proof(),
                        Proof::Script(tactics)
                            if TacticCertificate::from_proof_tactics(tactics).is_ok()
                    )
                {
                    return Err(ClickError::new(
                        "`immutable` and `mutable` region proof clauses must use the default prover, `by auto;`, `by frame;`, or a surface certificate",
                    ));
                }
            } else if item.kind() == StructuralItemKind::Invariant {
                debug_assert!(item.proof().is_auto_tactic());
            } else if !item.proof().is_auto_tactic()
                && !matches!(item.proof(), Proof::Script(_))
            {
                return Err(ClickError::new(
                    "`assert` structural clauses must use the default prover, `by auto;`, or a supported pure proof script",
                ));
            }
            if item.kind() == StructuralItemKind::Assert
                && click_proposition_to_c_expression(
                    item.proposition()
                        .expect("assert structural item should contain a proposition"),
                )
                .is_none()
            {
                return Err(ClickError::new(
                    "`assert` clauses currently support executable propositions only",
                ));
            }
        }
    }
    Ok(())
}

fn validate_loop_phase_proof(phase: &str, proof: Option<&Proof>) -> Result<(), ClickError> {
    let Some(Proof::Script(tactics)) = proof else {
        return Ok(());
    };
    if phase == "preserve" {
        return Ok(());
    }
    validate_loop_initialization_tactics(tactics)
}

fn validate_loop_initialization_tactics(tactics: &[ProofTactic]) -> Result<(), ClickError> {
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::Have(_)
            | ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Rewrite(_)
            | ProofTactic::Simp => {}
            ProofTactic::If(proof_if) => {
                validate_loop_initialization_tactics(&proof_if.then_tactics)?;
                validate_loop_initialization_tactics(&proof_if.else_tactics)?;
            }
            tactic => {
                return Err(ClickError::new(format!(
                    "`initialize` is a pure proof and cannot use `{}`",
                    validation::tactic_name(tactic)
                )));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;
