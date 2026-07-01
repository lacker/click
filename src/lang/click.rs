//! Tiny `.click` sidecar verifier for the C0 kernel path.
//!
//! This is intentionally a first slice, not the final Click language. It gives
//! us a source-file-shaped workflow for C examples while leaving the larger
//! tactic language design open.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::kernel::{
    Assumptions, Bitvector32Term, CComparisonOperator, CExpression, CExpressionOutcome, CFunction,
    CFunctionEnvironment, CFunctionOutcome, CFunctionSpecification, CLoopEffect, CLoopEffectCheck,
    CLoopEffectSpan, CLoopInvariantCheck, CMemory, CMemoryRange, CMemorySegment, CResource,
    CResourceSpec, CState, CStatement, CType, CValue, ConditionTerm, PathFact, Pointer,
    PointerOffsetTerm, ProofObligation, Proposition, ResourceContext, Sort, SpecExpression,
    SpecMemory, SpecProposition, Term, Theorem, Variable, c_function, c_function_specification,
    c_labeled_assert, c_pointer_value, c_seq, c_while_with_invariant_and_effect_checks,
    prove_c_function_satisfies_specification_from_symbolic_path,
    prove_c_function_satisfies_specification_with_environment,
    prove_symbolic_c_function_execution_paths_with_environment,
    prove_symbolic_c_function_verification_paths_with_environment,
    substitute_int32_variable_in_proposition,
};
use crate::lang::c::syntax::{self, C0Expression, C0Type};

mod parser;
use parser::ContractLetBinding;

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
    kind: ResourceKind,
    representation: Option<ResourceRepresentation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResourceRepresentation {
    contains: Vec<ResourceClause>,
    invariants: Vec<ClickProposition>,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResourceKind {
    Affine,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionBlock {
    signature: FunctionSignature,
    requires: Vec<Requirement>,
    structural_clauses: Vec<StructuralClause>,
    effects: Vec<EffectClause>,
    ensures: Vec<EnsureClause>,
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Requirement {
    Labeled {
        label: String,
        requirement: Box<Requirement>,
    },
    ValidRange {
        name: String,
        bytes: RangeBytes,
    },
    ValidRangeSegment {
        segment: ContractSegment,
    },
    Disjoint {
        left: ContractSegment,
        right: ContractSegment,
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
    Free(ContractSegment),
    Named {
        name: String,
        arguments: Vec<ContractExpression>,
        parameter_types: Vec<C0Type>,
    },
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
}

impl Default for SpecElaborationContext {
    fn default() -> Self {
        Self {
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            current_memory: SpecMemory::Current,
            current_loop_entry: None,
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

    fn old_state(
        &self,
        entry_values: &BTreeMap<String, CValue>,
        entry_memory: &CMemory,
    ) -> Result<Self, String> {
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
///
/// `auto` is a heuristic tactic. Deterministic proof replay should grow through
/// `Proof::Steps`, where each `ProofStep` is an explicit axiom invocation or a
/// fixed deterministic sequence of axiom invocations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
    Tactic(Tactic),
    Steps(Vec<ProofStep>),
}

/// A deterministic `.click` proof step.
///
/// This is intentionally separate from `Tactic`: tactics may search, but proof
/// steps should be stable and replayable. Successful tactics can attach these
/// steps as replayable proof certificates.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofStep {
    SymbolicExecute,
    BoundedExecute,
    LoopVc(CodeRegionRef),
    Frame(Option<CodeRegionRef>),
    Unfold(String),
    ApplyTheorem(TheoremApplication),
    OpenResource(ResourceClause),
    CloseResource(ResourceClause),
    Witness(ProofWitness),
    Choose(ProofChoice),
    Simp,
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

/// A `.click` tactic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Tactic {
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
    pub proof_steps: Option<Vec<ProofStep>>,
    pub specification: CFunctionSpecification,
    pub theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedPureTheorem {
    pub theorem_definition: TheoremDefinition,
    pub ensure_index: usize,
    pub ensure_clause: EnsureClause,
    pub proof_kind: ProofKind,
    pub proof_steps: Option<Vec<ProofStep>>,
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
    ProofSteps,
    LoopVerification,
    BoundedExecution,
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

    pub fn kind(&self) -> ResourceKind {
        self.kind
    }

    pub fn representation(&self) -> Option<&ResourceRepresentation> {
        self.representation.as_ref()
    }
}

impl ResourceRepresentation {
    pub fn contains(&self) -> &[ResourceClause] {
        &self.contains
    }

    pub fn invariants(&self) -> &[ClickProposition] {
        &self.invariants
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
        matches!(self, Self::Tactic(Tactic::Auto))
    }

    pub fn is_frame_tactic(&self) -> bool {
        matches!(self, Self::Tactic(Tactic::Frame))
    }

    pub fn is_auto_or_frame_tactic(&self) -> bool {
        self.is_auto_tactic() || self.is_frame_tactic()
    }

    fn is_unfold_only_steps(&self) -> bool {
        matches!(
            self,
            Self::Steps(steps)
                if !steps.is_empty()
                    && steps.iter().all(|step| matches!(step, ProofStep::Unfold(_)))
        )
    }

    fn unfold_step_names(&self) -> Vec<String> {
        match self {
            Self::Steps(steps) => steps
                .iter()
                .filter_map(|step| match step {
                    ProofStep::Unfold(name) => Some(name.clone()),
                    _ => None,
                })
                .collect(),
            Self::Tactic(_) => Vec::new(),
        }
    }

    pub fn tactic(&self) -> Option<&Tactic> {
        match self {
            Self::Tactic(tactic) => Some(tactic),
            Self::Steps(_) => None,
        }
    }

    pub fn steps(&self) -> Option<&[ProofStep]> {
        match self {
            Self::Tactic(_) => None,
            Self::Steps(steps) => Some(steps),
        }
    }
}

impl VerifiedCTheorem {
    pub fn proof_kind(&self) -> ProofKind {
        self.proof_kind
    }

    pub fn proof_steps(&self) -> Option<&[ProofStep]> {
        self.proof_steps.as_deref()
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

pub fn verify_c0_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let file = parse(click_source)?;
    let c_sources: BTreeMap<&str, &str> = c_sources.iter().copied().collect();
    let parsed_sources = parse_verified_sources(&file, &c_sources)?;
    let function_environment = build_function_environment(&parsed_sources, file.function_blocks())?;
    let predicate_definitions = combined_predicate_definitions(&file)?;
    let click_function_definitions = combined_click_function_definitions(&file)?;
    let resource_definitions = combined_resource_definitions(&file)?;
    let theorem_definitions = combined_theorem_definitions(&file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);
    let resource_environment = ResourceEnvironment::new(&resource_definitions);
    let _verified_theorems = verify_theorem_definitions(
        &theorem_definitions,
        &predicate_environment,
        &click_function_environment,
    )?;
    let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
    let mut verified = Vec::new();

    for function_block in file.function_blocks {
        let (source_path, parsed_function) = parsed_sources
            .get(function_block.signature.name())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{}` is not defined by any `verifying` source",
                    function_block.signature.name()
                ))
            })?;
        check_signature(&function_block.signature, parsed_function, source_path)?;
        validate_structural_clauses(&function_block, parsed_function)?;
        for claim in function_claims(&function_block) {
            let claim_label = function_claim_label(function_block.signature.name(), &claim);
            match claim.proof() {
                Proof::Tactic(Tactic::Auto) => {
                    let theorems = prove_claim_by_auto(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?;
                    verified.extend(theorems);
                }
                Proof::Tactic(Tactic::Frame) => {
                    let theorems = prove_claim_by_frame(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?;
                    verified.extend(theorems);
                }
                Proof::Tactic(Tactic::Simp) => {
                    let theorems = prove_claim_by_simp(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?;
                    verified.extend(theorems);
                }
                Proof::Steps(steps) => {
                    let theorems = prove_claim_by_steps(
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                        steps,
                    )?;
                    verified.extend(theorems);
                }
            }
        }
    }

    Ok(verified)
}

fn verify_theorem_definitions(
    theorem_definitions: &[TheoremDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let mut verified = Vec::new();
    let mut theorem_environment = TheoremEnvironment::new(&[]);
    for theorem in theorem_definitions {
        let context =
            pure_theorem_context(theorem, predicate_environment, click_function_environment)?;
        for (ensure_index, ensure_clause) in theorem.ensures().iter().enumerate() {
            let claim_label = theorem_claim_label(theorem.name(), ensure_index, ensure_clause);
            let theorem = verify_theorem_ensure(
                theorem,
                ensure_index,
                ensure_clause,
                &claim_label,
                &context,
                predicate_environment,
                click_function_environment,
                &theorem_environment,
            )?;
            verified.push(theorem);
        }
        theorem_environment.insert(theorem.clone());
    }
    Ok(verified)
}

#[derive(Clone, Debug)]
struct PureTheoremContext {
    memory: CMemory,
    values: BTreeMap<String, CValue>,
    array_refs: ClickArrayRefs,
    requires: Vec<Proposition>,
}

fn pure_theorem_context(
    theorem: &TheoremDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<PureTheoremContext, ClickError> {
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(theorem.parameters());
    let array_refs = pure_theorem_array_refs(theorem.parameters(), &values, &memory);
    let requires = theorem
        .requires()
        .iter()
        .map(|requirement| {
            let Some(proposition) = requirement.proposition() else {
                return Err(ClickError::new(format!(
                    "pure theorem `{}` currently supports proposition `requires` clauses only",
                    theorem.name()
                )));
            };
            lower_pure_theorem_proposition(
                theorem.name(),
                proposition,
                &values,
                &array_refs,
                &memory,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "theorem `{}` setup failed: could not lower requirement: {message}",
                    theorem.name()
                ))
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(PureTheoremContext {
        memory,
        values,
        array_refs,
        requires,
    })
}

fn pure_theorem_parameter_values(parameters: &[FunctionParameter]) -> BTreeMap<String, CValue> {
    parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let value = match parameter.c_type() {
                C0Type::Int32 => CValue::Int32(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::UInt8 => CValue::UInt8(Bitvector32Term::Variable(Variable(index as u64))),
                C0Type::Int32Pointer | C0Type::Int32Array(_) => CValue::Pointer(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }),
                C0Type::UInt8Pointer | C0Type::UInt8Array(_) => CValue::Pointer(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                }),
            };
            (parameter.name().to_string(), value)
        })
        .collect()
}

fn pure_theorem_array_refs(
    parameters: &[FunctionParameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.c_type())?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

fn theorem_claim_label(
    theorem_name: &str,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
) -> String {
    match ensure_clause.name() {
        Some(name) => format!("{theorem_name}.{name}"),
        None => format!("{theorem_name}.ensures_{ensure_index}"),
    }
}

fn verify_theorem_ensure(
    theorem: &TheoremDefinition,
    ensure_index: usize,
    ensure_clause: &EnsureClause,
    claim_label: &str,
    context: &PureTheoremContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<VerifiedPureTheorem, ClickError> {
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(format!(
            "pure theorem `{}` currently supports proposition `ensures` clauses only",
            theorem.name()
        )));
    };
    let goal = lower_pure_theorem_proposition(
        theorem.name(),
        surface_goal,
        &context.values,
        &context.array_refs,
        &context.memory,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` failed: could not lower conclusion: {message}"
        ))
    })?;

    match ensure_clause.proof() {
        Proof::Tactic(Tactic::Auto) => {
            prove_pure_theorem_goal(
                claim_label,
                "auto",
                &context.requires,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                context,
                &[],
                &[],
                true,
            )?;
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::Pure,
                proof_steps: None,
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
        Proof::Tactic(Tactic::Simp) => {
            prove_pure_theorem_goal(
                claim_label,
                "simp",
                &context.requires,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                context,
                &[],
                &[],
                true,
            )?;
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::Simp,
                proof_steps: None,
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
        Proof::Tactic(Tactic::Frame) => Err(ClickError::new(format!(
            "`frame` cannot prove pure theorem `{claim_label}`"
        ))),
        Proof::Steps(steps) => {
            if steps.is_empty() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` has an empty proof-step script"
                )));
            }
            let mut unfolded_predicates = Vec::new();
            let mut theorem_applications = Vec::new();
            let mut use_simp = false;
            for (step_index, step) in steps.iter().enumerate() {
                match step {
                    ProofStep::Unfold(name) => {
                        if predicate_environment.get(name).is_none() {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` proof step {step_index}: unknown predicate `{name}`"
                            )));
                        }
                        if !unfolded_predicates.contains(name) {
                            unfolded_predicates.push(name.clone());
                        }
                    }
                    ProofStep::ApplyTheorem(application) => {
                        if theorem_environment.get(&application.name).is_none() {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` proof step {step_index}: unknown theorem `{}`",
                                application.name
                            )));
                        }
                        theorem_applications.push((step_index, application.clone()));
                    }
                    ProofStep::Simp => {
                        use_simp = true;
                    }
                    _ => {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` proof step {step_index}: `{}` cannot prove a pure theorem",
                            proof_step_name(step)
                        )));
                    }
                }
            }
            prove_pure_theorem_goal(
                claim_label,
                "proof steps",
                &context.requires,
                &goal,
                predicate_environment,
                click_function_environment,
                theorem_environment,
                context,
                &theorem_applications,
                &unfolded_predicates,
                use_simp,
            )?;
            Ok(VerifiedPureTheorem {
                theorem_definition: theorem.clone(),
                ensure_index,
                ensure_clause: ensure_clause.clone(),
                proof_kind: ProofKind::ProofSteps,
                proof_steps: Some(steps.to_vec()),
                requires: context.requires.clone(),
                conclusion: goal,
            })
        }
    }
}

fn lower_pure_theorem_proposition(
    theorem_name: &str,
    proposition: &ClickProposition,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let mut lowerer = KernelPropositionLowerer::new(
        values.clone(),
        array_refs.clone(),
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    lowerer
        .lower_requirement_proposition(proposition)
        .map_err(|error| {
            error
                .message()
                .replace("`requires`", &format!("pure theorem `{theorem_name}`"))
        })
}

fn prove_pure_theorem_goal(
    claim_label: &str,
    proof_name: &str,
    requires: &[Proposition],
    goal: &Proposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    theorem_environment: &TheoremEnvironment,
    context: &PureTheoremContext,
    theorem_applications: &[(usize, TheoremApplication)],
    unfolded_predicates: &[String],
    use_simp: bool,
) -> Result<(), ClickError> {
    let mut available = unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        requires,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` failed: {message}")))?;
    let state = CState::new().with_memory(context.memory.clone());
    let application_context = TheoremApplicationContext {
        values: &context.values,
        array_refs: &context.array_refs,
        pre_state: &state,
        post_state: &state,
        result: None,
    };
    available = apply_theorem_applications_to_available(
        theorem_environment,
        theorem_applications,
        claim_label,
        None,
        available,
        &application_context,
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
    )?;
    let assumptions = assumptions_from_propositions(&available);
    let goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        goal,
        &assumptions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` failed: {message}")))?;
    let assumptions = assumptions_from_propositions(&available);
    if assumptions.proves(&goal) {
        return Ok(());
    }
    if use_simp {
        match simp_proposition(&goal, &assumptions) {
            SimpProposition::True => return Ok(()),
            simplified => {
                return Err(ClickError::new(format!(
                    "`{proof_name}` failed for `{claim_label}`: simplified proposition was not true: {simplified:?}\n  goal: {goal:?}\n  available requirements: {}",
                    describe_propositions(&available)
                )));
            }
        }
    }

    Err(ClickError::new(format!(
        "`{proof_name}` failed for `{claim_label}`: proposition was not provable\n  goal: {goal:?}\n  available requirements: {}",
        describe_propositions(&available)
    )))
}

struct TheoremApplicationContext<'a> {
    values: &'a BTreeMap<String, CValue>,
    array_refs: &'a ClickArrayRefs,
    pre_state: &'a CState,
    post_state: &'a CState,
    result: Option<&'a CValue>,
}

fn apply_theorem_applications_to_available(
    theorem_environment: &TheoremEnvironment,
    theorem_applications: &[(usize, TheoremApplication)],
    claim_label: &str,
    path_index: Option<usize>,
    mut available: Vec<Proposition>,
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    for (step_index, application) in theorem_applications {
        available = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &available,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, *step_index, message)
        })?;
        let conclusions = instantiate_theorem_application(
            theorem_environment,
            application,
            claim_label,
            path_index,
            *step_index,
            &available,
            context,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )?;
        for conclusion in conclusions {
            if !available.contains(&conclusion) {
                available.push(conclusion);
            }
        }
    }
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &available,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, 0, message))
}

fn instantiate_theorem_application(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    claim_label: &str,
    path_index: Option<usize>,
    step_index: usize,
    available: &[Proposition],
    context: &TheoremApplicationContext<'_>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<Vec<Proposition>, ClickError> {
    let theorem = theorem_environment.get(&application.name).ok_or_else(|| {
        theorem_application_error(
            claim_label,
            path_index,
            step_index,
            format!("unknown theorem `{}`", application.name),
        )
    })?;
    if application.arguments.len() != theorem.parameters().len() {
        return Err(theorem_application_error(
            claim_label,
            path_index,
            step_index,
            format!(
                "theorem `{}` expects {} argument(s), got {}",
                theorem.name(),
                theorem.parameters().len(),
                application.arguments.len()
            ),
        ));
    }

    let assumptions = assumptions_from_propositions(available);
    let (values, array_refs) = theorem_application_bindings(
        theorem,
        application,
        context,
        &assumptions,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| theorem_application_error(claim_label, path_index, step_index, message))?;
    let mut lowerer = KernelPropositionLowerer::new(
        values,
        array_refs,
        context.post_state.memory().clone(),
        predicate_environment,
        click_function_environment,
    );

    for requirement in theorem.requires() {
        let Some(requirement) = requirement.proposition() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                step_index,
                format!(
                    "theorem `{}` has a non-proposition requirement that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let mut lowered = lowerer
            .lower_requirement_proposition(requirement)
            .map_err(|error| {
                theorem_application_error(
                    claim_label,
                    path_index,
                    step_index,
                    format!(
                        "could not lower theorem `{}` requirement: {}",
                        theorem.name(),
                        error.message()
                    ),
                )
            })?;
        lowered = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &lowered,
            &assumptions,
        )
        .map_err(|message| {
            theorem_application_error(claim_label, path_index, step_index, message)
        })?;
        if !assumptions.proves(&lowered)
            && !matches!(
                simp_proposition(&lowered, &assumptions),
                SimpProposition::True
            )
        {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                step_index,
                format!(
                    "could not prove requirement for theorem `{}`: {lowered:?}\n  available requirements: {}",
                    theorem.name(),
                    describe_propositions(available)
                ),
            ));
        }
    }

    let mut conclusions = Vec::new();
    for ensure in theorem.ensures() {
        let Ensure::Proposition(conclusion) = ensure.ensure() else {
            return Err(theorem_application_error(
                claim_label,
                path_index,
                step_index,
                format!(
                    "theorem `{}` has a non-proposition conclusion that cannot be applied here",
                    theorem.name()
                ),
            ));
        };
        let conclusion = lowerer
            .lower_requirement_proposition(conclusion)
            .map_err(|error| {
                theorem_application_error(
                    claim_label,
                    path_index,
                    step_index,
                    format!(
                        "could not lower theorem `{}` conclusion: {}",
                        theorem.name(),
                        error.message()
                    ),
                )
            })?;
        conclusions.push(conclusion);
    }
    Ok(conclusions)
}

fn theorem_application_bindings(
    theorem: &TheoremDefinition,
    application: &TheoremApplication,
    context: &TheoremApplicationContext<'_>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let mut active_functions = BTreeSet::new();
    let mut values = BTreeMap::new();
    let mut array_refs = BTreeMap::new();
    for (parameter, argument) in theorem.parameters().iter().zip(&application.arguments) {
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                &mut active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "theorem `{}` parameter `{}` is not an array-ref parameter",
                        theorem.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    theorem.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            values.insert(
                parameter.name().to_string(),
                CValue::Pointer(array_ref.pointer.clone()),
            );
            array_refs.insert(parameter.name().to_string(), array_ref);
        } else {
            let value = evaluate_contract_expression_with_environment(
                context.values,
                context.array_refs,
                context.pre_state,
                context.post_state,
                context.result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                &mut active_functions,
            )?;
            if !c_value_matches_click_type(&value, parameter.c_type()) {
                return Err(format!(
                    "theorem `{}` parameter `{}` expects {}, got {value:?}",
                    theorem.name(),
                    parameter.name(),
                    describe_c0_type(parameter.c_type())
                ));
            }
            values.insert(parameter.name().to_string(), value);
        }
    }
    Ok((values, array_refs))
}

fn theorem_application_error(
    claim_label: &str,
    path_index: Option<usize>,
    step_index: usize,
    message: impl Into<String>,
) -> ClickError {
    let path = path_index
        .map(|index| format!(" path {index},"))
        .unwrap_or_default();
    ClickError::new(format!(
        "`{claim_label}`{path} proof step {step_index}: `apply` failed: {}",
        message.into()
    ))
}

#[derive(Clone, Copy)]
enum FunctionClaimRef<'a> {
    Effect(usize, &'a EffectClause),
    Ensure(usize, &'a EnsureClause),
}

impl<'a> FunctionClaimRef<'a> {
    fn proof(self) -> &'a Proof {
        match self {
            Self::Effect(_, clause) => clause.proof(),
            Self::Ensure(_, clause) => clause.proof(),
        }
    }

    fn verified_claim(self) -> VerifiedClaim {
        match self {
            Self::Effect(index, clause) => VerifiedClaim::Effect {
                index,
                clause: clause.clone(),
            },
            Self::Ensure(index, clause) => VerifiedClaim::Ensure {
                index,
                clause: clause.clone(),
            },
        }
    }
}

fn function_claims(function_block: &FunctionBlock) -> Vec<FunctionClaimRef<'_>> {
    function_block
        .effects()
        .iter()
        .enumerate()
        .map(|(index, clause)| FunctionClaimRef::Effect(index, clause))
        .chain(
            function_block
                .ensures()
                .iter()
                .enumerate()
                .map(|(index, clause)| FunctionClaimRef::Ensure(index, clause)),
        )
        .collect()
}

fn prove_claim_by_auto(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let (state, arguments, requirement_propositions) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    let requirement_propositions = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_propositions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
    )?;
    let assumptions = assumptions_from_propositions(&requirement_propositions);
    let vc_execution = prove_symbolic_c_function_verification_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions.clone(),
        function_environment.clone(),
    );
    if let Some(error) =
        execution_obligation_error(&vc_execution, claim_label, &requirement_propositions)
    {
        return Err(error);
    }
    let loop_verification_error = match prove_claim_from_execution(
        &vc_execution,
        AutoExecutionKind::LoopVerification,
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_propositions,
        predicate_environment,
        click_function_environment,
    ) {
        Ok(theorems) => {
            let proof_steps = certified_proof_steps(
                source_path,
                function_block,
                parsed_function,
                claim,
                claim_label,
                function_environment,
                predicate_environment,
                click_function_environment,
                resource_environment,
                theorem_environment,
                auto_loop_verification_proof_step_candidates(function_block, claim),
            );
            return Ok(with_proof_steps(theorems, proof_steps));
        }
        Err(error) => Some(error),
    };
    let execution = prove_symbolic_c_function_execution_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
    );
    if let Some(error) =
        execution_obligation_error(&execution, claim_label, &requirement_propositions)
    {
        if let Some(loop_verification_error) = loop_verification_error {
            return Err(loop_verification_error);
        }
        return Err(error);
    }
    let theorems = prove_claim_from_execution(
        &execution,
        AutoExecutionKind::BoundedExecution {
            environment: function_environment,
        },
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_propositions,
        predicate_environment,
        click_function_environment,
    )?;
    let proof_steps = certified_proof_steps(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        bounded_execution_proof_step_candidates(claim),
    );
    Ok(with_proof_steps(theorems, proof_steps))
}

fn prove_claim_by_frame(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
        return Err(ClickError::new(format!(
            "`frame` only proves effect clauses for `{claim_label}`; use `by auto;` or `by simp;` for postconditions"
        )));
    }

    let (state, arguments, requirement_propositions) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    let requirement_propositions = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_propositions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
    )?;
    let assumptions = assumptions_from_propositions(&requirement_propositions);
    let execution = prove_symbolic_c_function_verification_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
    );
    if let Some(error) = execution_obligation_error_for_tactic(
        "frame",
        &execution,
        claim_label,
        &requirement_propositions,
    ) {
        return Err(error);
    }

    let theorems = prove_claim_from_execution(
        &execution,
        AutoExecutionKind::Frame,
        source_path,
        function_block,
        claim,
        claim_label,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_propositions,
        predicate_environment,
        click_function_environment,
    )?;
    let proof_steps = certified_proof_steps(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        frame_proof_step_candidates(),
    );
    Ok(with_proof_steps(theorems, proof_steps))
}

fn prove_claim_by_simp(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if count_loops(parsed_function.body()) != 0 {
        return Err(ClickError::new(format!(
            "`simp` does not prove loop-backed claims for `{claim_label}`; use `by auto;`"
        )));
    }

    let (state, arguments, requirement_propositions) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    let requirement_propositions = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_propositions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
    )?;
    let proof_steps = certified_proof_steps(
        source_path,
        function_block,
        parsed_function,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        vec![vec![ProofStep::SymbolicExecute, ProofStep::Simp]],
    );
    let assumptions = assumptions_from_propositions(&requirement_propositions);
    let execution = prove_symbolic_c_function_execution_paths_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        assumptions,
        function_environment.clone(),
    );
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`simp` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`simp` could not establish a direct execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`simp` failed for `{claim_label}` path {path_index}: execution left obligations: {}\n  available requirements: {}\n  path facts: {}",
                describe_obligations(path.obligations()),
                describe_propositions(&requirement_propositions),
                describe_facts(path.facts())
            )));
        }

        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`simp` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  available requirements: {}\n  path facts: {}",
                    describe_propositions(&requirement_propositions),
                    describe_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_propositions.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_function_claim_by_simp(
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            claim,
            parsed_function.parameters(),
            &arguments,
            &state,
            &outcome,
            predicate_environment,
            click_function_environment,
            &[],
        )?;
        let specification = c_function_specification(
            state.clone(),
            arguments.clone(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = prove_c_function_satisfies_specification_with_environment(
            function.clone(),
            specification.clone(),
            Assumptions::new(),
            function_environment.clone(),
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`simp` failed for `{claim_label}` path {path_index}: execution did not satisfy the packaged specification\n  path facts: {}",
                describe_facts(path.facts())
            ))
        })?;

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind: ProofKind::Simp,
            proof_steps: proof_steps.clone(),
            specification,
            theorem,
        });
    }

    Ok(verified)
}

#[derive(Default)]
struct ProofStepReplayState {
    execution: Option<crate::kernel::SymbolicCExecution>,
    execution_mode: Option<ProofStepExecutionMode>,
    loop_vcs: BTreeSet<usize>,
    frames: BTreeSet<Option<CodeRegionRef>>,
    unfolded_predicates: Vec<String>,
    theorem_applications: Vec<(usize, TheoremApplication)>,
    resource_closes: Vec<ResourceClause>,
    simp: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProofStepExecutionMode {
    Verification,
    Bounded,
}

fn prove_claim_by_steps(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    steps: &[ProofStep],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if steps.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` has an empty proof-step script"
        )));
    }

    let (mut state, arguments, mut requirement_propositions) = initial_call(
        function_block.signature.name(),
        function_block.requires(),
        parsed_function.parameters(),
        predicate_environment,
        click_function_environment,
    )?;
    requirement_propositions = requirements_with_structural_unfolds(
        predicate_environment,
        click_function_environment,
        function_block,
        &requirement_propositions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    let function = annotated_function(
        function_block,
        parsed_function,
        &state,
        &arguments,
        predicate_environment,
        click_function_environment,
    )?;
    let mut assumptions = assumptions_from_propositions(&requirement_propositions);
    let mut replay = ProofStepReplayState::default();

    for (step_index, step) in steps.iter().enumerate() {
        match step {
            ProofStep::OpenResource(resource) => {
                if replay.execution.is_some() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `open` must run before `symbolic_execute()` or `bounded_execute()`"
                    )));
                }
                state = open_represented_resource(
                    resource_environment,
                    resource,
                    parsed_function.parameters(),
                    &arguments,
                    state,
                    &mut requirement_propositions,
                    predicate_environment,
                    click_function_environment,
                    claim_label,
                    step_index,
                )?;
                assumptions = assumptions_from_propositions(&requirement_propositions);
            }
            ProofStep::SymbolicExecute => {
                set_replay_execution(
                    &mut replay,
                    ProofStepExecutionMode::Verification,
                    claim_label,
                    step_index,
                    "symbolic_execute",
                    prove_symbolic_c_function_verification_paths_with_environment(
                        state.clone(),
                        function.clone(),
                        arguments.clone(),
                        assumptions.clone(),
                        function_environment.clone(),
                    ),
                )?;
            }
            ProofStep::BoundedExecute => {
                set_replay_execution(
                    &mut replay,
                    ProofStepExecutionMode::Bounded,
                    claim_label,
                    step_index,
                    "bounded_execute",
                    prove_symbolic_c_function_execution_paths_with_environment(
                        state.clone(),
                        function.clone(),
                        arguments.clone(),
                        assumptions.clone(),
                        function_environment.clone(),
                    ),
                )?;
            }
            ProofStep::LoopVc(region_ref) => {
                require_step_execution(&replay, claim_label, step_index, "loop_vc")?;
                require_verification_execution(&replay, claim_label, step_index, "loop_vc")?;
                let code_region =
                    resolve_code_region_ref(function_block, region_ref, claim_label, step_index)?;
                let CodeRegion::Loop(loop_index) = code_region else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: `loop_vc` expects a loop code region"
                    )));
                };
                validate_loop_code_region(parsed_function, loop_index, claim_label, step_index)?;
                validate_loop_vc_step(
                    replay.execution.as_ref().expect("execution should exist"),
                    loop_index,
                    claim_label,
                    step_index,
                )?;
                replay.loop_vcs.insert(loop_index);
            }
            ProofStep::Frame(region_ref) => {
                require_step_execution(&replay, claim_label, step_index, "frame")?;
                let code_region = region_ref
                    .as_ref()
                    .map(|region_ref| {
                        resolve_code_region_ref(function_block, region_ref, claim_label, step_index)
                    })
                    .transpose()?;
                validate_frame_code_region(
                    function_block,
                    parsed_function,
                    code_region,
                    claim,
                    claim_label,
                    step_index,
                )?;
                match code_region {
                    None | Some(CodeRegion::Function) => {
                        validate_function_frame_step(
                            replay.execution.as_ref().expect("execution should exist"),
                            claim,
                            claim_label,
                            step_index,
                            parsed_function.parameters(),
                            &arguments,
                            &state,
                            &requirement_propositions,
                        )?;
                    }
                    Some(CodeRegion::Loop(_)) => {
                        require_verification_execution(&replay, claim_label, step_index, "frame")?;
                    }
                    Some(CodeRegion::Statement(_)) => {}
                }
                replay.frames.insert(region_ref.clone());
            }
            ProofStep::Unfold(name) => {
                if predicate_environment.get(name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: unknown predicate `{name}`"
                    )));
                }
                if !replay.unfolded_predicates.contains(name) {
                    replay.unfolded_predicates.push(name.clone());
                }
            }
            ProofStep::ApplyTheorem(application) => {
                require_step_execution(&replay, claim_label, step_index, "apply")?;
                if theorem_environment.get(&application.name).is_none() {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` proof step {step_index}: unknown theorem `{}`",
                        application.name
                    )));
                }
                replay
                    .theorem_applications
                    .push((step_index, application.clone()));
            }
            ProofStep::CloseResource(resource) => {
                require_step_execution(&replay, claim_label, step_index, "close")?;
                replay.resource_closes.push(resource.clone());
            }
            ProofStep::Witness(_) => {
                require_step_execution(&replay, claim_label, step_index, "witness")?;
            }
            ProofStep::Choose(_) => {
                require_step_execution(&replay, claim_label, step_index, "choose")?;
            }
            ProofStep::Simp => {
                require_step_execution(&replay, claim_label, step_index, "simp")?;
                replay.simp = true;
            }
        }
    }

    let execution = replay.execution.as_ref().ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` proof-step script must run `symbolic_execute()` or `bounded_execute()`"
        ))
    })?;
    prove_claim_from_steps_execution(
        execution,
        replay
            .execution_mode
            .expect("proof-step execution should have an execution mode"),
        source_path,
        function_block,
        claim,
        claim_label,
        function_environment,
        predicate_environment,
        click_function_environment,
        resource_environment,
        theorem_environment,
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_propositions,
        &replay.unfolded_predicates,
        &replay.theorem_applications,
        &replay.resource_closes,
        replay.simp,
        steps,
    )
}

fn set_replay_execution(
    replay: &mut ProofStepReplayState,
    mode: ProofStepExecutionMode,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
    execution: crate::kernel::SymbolicCExecution,
) -> Result<(), ClickError> {
    if let Some(existing) = replay.execution_mode {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` cannot run after {existing:?} execution was already started"
        )));
    }
    replay.execution = Some(execution);
    replay.execution_mode = Some(mode);
    Ok(())
}

fn require_step_execution(
    replay: &ProofStepReplayState,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
) -> Result<(), ClickError> {
    if replay.execution.is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` requires `symbolic_execute()` first"
        )));
    }
    Ok(())
}

fn require_verification_execution(
    replay: &ProofStepReplayState,
    claim_label: &str,
    step_index: usize,
    step_name: &str,
) -> Result<(), ClickError> {
    if replay.execution_mode != Some(ProofStepExecutionMode::Verification) {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{step_name}` requires `symbolic_execute()` rather than `bounded_execute()`"
        )));
    }
    Ok(())
}

fn open_represented_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_propositions: &mut Vec<Proposition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    claim_label: &str,
    step_index: usize,
) -> Result<CState, ClickError> {
    let definition = represented_resource_definition(
        resource_environment,
        resource,
        "open",
        claim_label,
        step_index,
    )?;
    let representation = definition
        .representation()
        .expect("represented_resource_definition should require a representation");
    let substitutions =
        resource_argument_substitutions(definition, resource, claim_label, step_index)?;
    let abstract_resource = lower_resource_clause(resource, parameters, arguments, state.memory())?;
    let assumptions = assumptions_from_propositions(available_propositions);
    let resources = state
        .resources()
        .clone()
        .without_resource(&abstract_resource, &assumptions)
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `open({})` is missing resource `{}`\n  available resources: {}",
                describe_resource_clause(resource),
                describe_resource(&abstract_resource, parameters, arguments),
                describe_resources(state.resources().resources(), parameters, arguments)
            ))
        })?;
    state = state.with_resource_context(resources);

    for contained in representation.contains() {
        let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: could not instantiate `open({})`: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let lowered = lower_resource_clause(&contained, parameters, arguments, state.memory())?;
        let memory = materialize_represented_resource_cells(
            state.memory().clone(),
            &contained,
            &lowered,
            parameters,
        );
        let resources = state.resources().clone().with_resource(lowered);
        state = state.with_memory(memory).with_resource_context(resources);
    }
    if let Some(duplicate) = state.resources().duplicate_named_resource() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `open({})` produced duplicate affine resource `{}`",
            describe_resource_clause(resource),
            describe_resource(duplicate, parameters, arguments)
        )));
    }

    for invariant in representation.invariants() {
        let invariant =
            substitute_click_proposition(invariant, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: could not instantiate `open({})` invariant: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
        let fact = lower_outcome_proposition(
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
            available_propositions,
            &invariant,
            predicate_environment,
            click_function_environment,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: could not lower `open({})` invariant: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        available_propositions.push(fact);
    }

    Ok(state)
}

fn close_represented_resources_on_outcome(
    resource_environment: &ResourceEnvironment,
    resource_closes: &[ResourceClause],
    claim_label: &str,
    path_index: usize,
    path_facts: &[PathFact],
    available_propositions: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    mut outcome: CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<CFunctionOutcome, ClickError> {
    for resource in resource_closes {
        let definition = represented_resource_definition(
            resource_environment,
            resource,
            "close",
            claim_label,
            path_index,
        )?;
        let representation = definition
            .representation()
            .expect("represented_resource_definition should require a representation");
        let substitutions =
            resource_argument_substitutions(definition, resource, claim_label, path_index)?;

        for invariant in representation.invariants() {
            let invariant =
                substitute_click_proposition(invariant, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `close({})` invariant: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            prove_ensure_proposition_by_simp(
                claim_label,
                path_index,
                path_facts,
                available_propositions,
                &invariant,
                parameters,
                arguments,
                pre_state,
                &outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `close({})` invariant failed: {}",
                    describe_resource_clause(resource),
                    error.message()
                ))
            })?;
        }

        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `close({})` requires a return outcome, got {}\n  path facts: {}",
                describe_resource_clause(resource),
                describe_function_outcome(&outcome, parameters, arguments),
                describe_facts(path_facts)
            )));
        };
        let mut post_state = state;
        let assumptions = assumptions_from_propositions(available_propositions);
        for contained in representation.contains() {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `close({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let lowered =
                lower_resource_clause(&contained, parameters, arguments, post_state.memory())?;
            let resources = post_state
                .resources()
                .clone()
                .without_resource(&lowered, &assumptions)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `close({})` is missing contained resource `{}`\n  final resources: {}\n  path facts: {}",
                        describe_resource_clause(resource),
                        describe_resource(&lowered, parameters, arguments),
                        describe_resources(post_state.resources().resources(), parameters, arguments),
                        describe_facts(path_facts)
                    ))
                })?;
            post_state = post_state.with_resource_context(resources);
        }

        let abstract_resource =
            lower_resource_clause(resource, parameters, arguments, post_state.memory())?;
        let resources = post_state
            .resources()
            .clone()
            .with_resource(abstract_resource.clone());
        post_state = post_state.with_resource_context(resources);
        if let Some(duplicate) = post_state.resources().duplicate_named_resource() {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `close({})` produced duplicate affine resource `{}`",
                describe_resource_clause(resource),
                describe_resource(duplicate, parameters, arguments)
            )));
        }
        outcome = CFunctionOutcome::Return {
            value,
            state: post_state,
        };
    }

    Ok(outcome)
}

fn represented_resource_definition<'a>(
    resource_environment: &'a ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    claim_label: &str,
    step_index: usize,
) -> Result<&'a ResourceDefinition, ClickError> {
    let ResourceClause::Named { name, .. } = resource else {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{action}` expects a named represented resource"
        )));
    };
    let definition = resource_environment.get(name).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: unknown resource `{name}`"
        ))
    })?;
    if definition.representation().is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `{action}` expects represented resource `{name}` to have a body"
        )));
    }
    Ok(definition)
}

fn resource_argument_substitutions(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    claim_label: &str,
    step_index: usize,
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    let ResourceClause::Named {
        name,
        arguments,
        parameter_types,
    } = resource
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: expected named resource"
        )));
    };
    if definition.name() != name {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: resource definition mismatch for `{name}`"
        )));
    }
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: resource `{name}` expects {} argument(s), got {}",
            definition.parameters().len(),
            arguments.len()
        )));
    }
    let expected_types = definition
        .parameters()
        .iter()
        .map(FunctionParameter::c_type)
        .collect::<Vec<_>>();
    if parameter_types != &expected_types {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: resource `{name}` has malformed argument type metadata"
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

fn instantiate_resource_clause(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Free(segment) => Ok(ResourceClause::Free(instantiate_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Named {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

fn instantiate_contract_segment(
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

fn materialize_represented_resource_cells(
    mut memory: CMemory,
    resource_clause: &ResourceClause,
    lowered: &CResource,
    parameters: &[syntax::C0Parameter],
) -> CMemory {
    let (segment, range) = match (resource_clause, lowered) {
        (ResourceClause::Read(segment), CResource::Read(range))
        | (ResourceClause::Write(segment), CResource::Write(range)) => (segment, range),
        _ => return memory,
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (range.start(), range.end())
    else {
        return memory;
    };
    if end < start {
        return memory;
    }

    let element_width = contract_segment_element_width(parameters, segment);
    let base_memory = memory.clone();
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            range.base().clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        let load =
            Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(pointer.clone()));
        let value = match element_width {
            1 => CValue::UInt8(load),
            _ => CValue::Int32(load),
        };
        memory = memory.store(pointer, value);
    }
    memory
}

fn resolve_code_region_ref(
    function_block: &FunctionBlock,
    region_ref: &CodeRegionRef,
    claim_label: &str,
    step_index: usize,
) -> Result<CodeRegion, ClickError> {
    Ok(match region_ref {
        CodeRegionRef::Function => CodeRegion::Function,
        CodeRegionRef::Loop(index) => CodeRegion::Loop(*index),
        CodeRegionRef::Statement(index) => CodeRegion::Statement(*index),
        CodeRegionRef::Label(label) => *function_block
            .structural_clauses()
            .iter()
            .find(|clause| clause.label() == Some(label.as_str()))
            .map(StructuralClause::region)
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: unknown code region label `{label}`"
                ))
            })?,
    })
}

fn validate_loop_code_region(
    parsed_function: &syntax::C0Function,
    loop_index: usize,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    if loop_index >= loop_count {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: function has no `loop({loop_index})` code region; it contains {loop_count} loop(s)"
        )));
    }
    Ok(())
}

fn validate_loop_vc_step(
    execution: &crate::kernel::SymbolicCExecution,
    loop_index: usize,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    let context_prefix = format!("loop {loop_index} ");
    let obligations = execution
        .paths()
        .iter()
        .flat_map(|path| path.obligations())
        .filter(|obligation| {
            obligation
                .context()
                .is_some_and(|context| context.starts_with(&context_prefix))
        })
        .cloned()
        .collect::<Vec<_>>();
    if !obligations.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `loop_vc(loop({loop_index}))` left obligations: {}",
            describe_obligations(&obligations)
        )));
    }
    Ok(())
}

fn validate_frame_code_region(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    code_region: Option<CodeRegion>,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    step_index: usize,
) -> Result<(), ClickError> {
    match code_region {
        None | Some(CodeRegion::Function) => {
            if matches!(claim, FunctionClaimRef::Ensure(_, _)) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `frame()` proves function-level effect claims; use `frame(loop(N))` or a code region label to use loop effect summaries in an `ensures` proof"
                )));
            }
            Ok(())
        }
        Some(CodeRegion::Loop(loop_index)) => {
            validate_loop_code_region(parsed_function, loop_index, claim_label, step_index)?;
            if !function_block.structural_clauses().iter().any(|clause| {
                clause.region() == &CodeRegion::Loop(loop_index)
                    && clause.items().iter().any(StructuralItem::is_effect_kind)
            }) {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `frame(loop({loop_index}))` needs a loop effect clause such as `mutable` or `immutable`"
                )));
            }
            Ok(())
        }
        Some(CodeRegion::Statement(statement_index)) => {
            let statement_count = count_statements(parsed_function.body());
            if statement_index >= statement_count {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: function has no `statement({statement_index})` code region; it contains {statement_count} statement(s)"
                )));
            }
            Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `frame(statement({statement_index}))` is not supported yet"
            )))
        }
    }
}

fn validate_function_frame_step(
    execution: &crate::kernel::SymbolicCExecution,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    step_index: usize,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    requirement_propositions: &[Proposition],
) -> Result<(), ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `frame()` hit execution limit {limit:?}"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` proof step {step_index}: `frame()` had no complete execution path"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}` proof step {step_index}: `frame()` left obligations on path {path_index}: {}",
                describe_obligations(path.obligations())
            )));
        }
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` proof step {step_index}: `frame()` saw unexpected theorem body {proposition:?}\n  path facts: {}",
                    describe_facts(path.facts())
                )));
            }
        };
        let mut path_requirements = requirement_propositions.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_function_claim(
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            &outcome,
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
            &[],
        )?;
    }

    Ok(())
}

fn prove_claim_from_steps_execution(
    execution: &crate::kernel::SymbolicCExecution,
    execution_mode: ProofStepExecutionMode,
    source_path: &str,
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_propositions: &[Proposition],
    unfolded_predicates: &[String],
    theorem_applications: &[(usize, TheoremApplication)],
    resource_closes: &[ResourceClause],
    use_simp: bool,
    proof_steps: &[ProofStep],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`proof steps` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`proof steps` could not prove any complete execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Err(ClickError::new(format!(
                "`proof steps` failed for `{claim_label}` path {path_index}: remaining proof obligations: {}\n  available requirements: {}\n  path facts: {}",
                describe_obligations(path.obligations()),
                describe_propositions(requirement_propositions),
                describe_facts(path.facts())
            )));
        }
        let mut outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`proof steps` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  available requirements: {}\n  path facts: {}",
                    describe_propositions(requirement_propositions),
                    describe_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_propositions.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        path_requirements = unfold_available_predicate_facts(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &path_requirements,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`proof steps` failed for `{claim_label}` path {path_index}: {message}"
            ))
        })?;
        outcome = close_represented_resources_on_outcome(
            resource_environment,
            resource_closes,
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            parameters,
            arguments,
            state,
            outcome,
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
        )?;
        if !theorem_applications.is_empty() {
            let CFunctionOutcome::Return {
                value: result,
                state: post_state,
            } = &outcome
            else {
                return Err(ClickError::new(format!(
                    "`proof steps` failed for `{claim_label}` path {path_index}: theorem application requires a return outcome, got {}\n  path facts: {}",
                    describe_function_outcome(&outcome, parameters, arguments),
                    describe_facts(path.facts())
                )));
            };
            let values = parameter_values(parameters, arguments).map_err(|error| {
                ClickError::new(format!(
                    "`proof steps` failed for `{claim_label}` path {path_index}: {}",
                    error.message
                ))
            })?;
            let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
            let application_context = TheoremApplicationContext {
                values: &values,
                array_refs: &array_refs,
                pre_state: state,
                post_state,
                result: Some(result),
            };
            path_requirements = apply_theorem_applications_to_available(
                theorem_environment,
                theorem_applications,
                claim_label,
                Some(path_index),
                path_requirements,
                &application_context,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )?;
        }
        let mut checking_requirements = path_requirements.clone();
        let has_existence_steps = proof_steps
            .iter()
            .any(|step| matches!(step, ProofStep::Witness(_) | ProofStep::Choose(_)));
        if has_existence_steps {
            check_function_claim_with_existence_steps(
                claim_label,
                path_index,
                path.facts(),
                &mut checking_requirements,
                claim,
                parameters,
                arguments,
                state,
                &outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                proof_steps,
                function_block.requires(),
                use_simp,
            )?;
        } else {
            if use_simp {
                check_function_claim_by_simp(
                    claim_label,
                    path_index,
                    path.facts(),
                    &path_requirements,
                    claim,
                    parameters,
                    arguments,
                    state,
                    &outcome,
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                )?;
            } else {
                check_function_claim(
                    claim_label,
                    path_index,
                    path.facts(),
                    &path_requirements,
                    claim,
                    parameters,
                    arguments,
                    state,
                    &outcome,
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                )?;
            }
        }
        let specification = c_function_specification(
            state.clone(),
            arguments.to_vec(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = match execution_mode {
            ProofStepExecutionMode::Verification => {
                prove_c_function_satisfies_specification_from_symbolic_path(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    path.facts(),
                    path.obligations(),
                )
            }
            ProofStepExecutionMode::Bounded => {
                prove_c_function_satisfies_specification_with_environment(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    function_environment.clone(),
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`proof steps` failed for `{claim_label}` path {path_index}: bounded execution did not satisfy the packaged specification\n  available requirements: {}\n  path facts: {}",
                        describe_propositions(&specification.requires()),
                        describe_facts(path.facts())
                    ))
                })?
            }
        };

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind: ProofKind::ProofSteps,
            proof_steps: Some(proof_steps.to_vec()),
            specification,
            theorem,
        });
    }

    Ok(verified)
}

enum AutoExecutionKind<'a> {
    Frame,
    LoopVerification,
    BoundedExecution {
        environment: &'a CFunctionEnvironment,
    },
}

impl AutoExecutionKind<'_> {
    fn proof_kind(&self) -> ProofKind {
        match self {
            Self::Frame => ProofKind::Frame,
            Self::LoopVerification => ProofKind::LoopVerification,
            Self::BoundedExecution { .. } => ProofKind::BoundedExecution,
        }
    }

    fn tactic_name(&self) -> &'static str {
        match self {
            Self::Frame => "frame",
            Self::LoopVerification | Self::BoundedExecution { .. } => "auto",
        }
    }
}

fn with_proof_steps(
    mut theorems: Vec<VerifiedCTheorem>,
    proof_steps: Option<Vec<ProofStep>>,
) -> Vec<VerifiedCTheorem> {
    if let Some(proof_steps) = proof_steps {
        for theorem in &mut theorems {
            theorem.proof_steps = Some(proof_steps.clone());
        }
    }
    theorems
}

fn requirements_with_structural_unfolds(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    function_block: &FunctionBlock,
    requirement_propositions: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    let unfolded_predicates = structural_unfold_step_names(function_block);
    unfold_available_predicate_facts(
        predicate_environment,
        click_function_environment,
        &unfolded_predicates,
        requirement_propositions,
    )
}

fn structural_unfold_step_names(function_block: &FunctionBlock) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for clause in function_block.structural_clauses() {
        for item in clause.items() {
            for name in item.proof().unfold_step_names() {
                if seen.insert(name.clone()) {
                    names.push(name);
                }
            }
        }
    }
    names
}

fn certified_proof_steps(
    source_path: &str,
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    function_environment: &CFunctionEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    theorem_environment: &TheoremEnvironment,
    candidates: Vec<Vec<ProofStep>>,
) -> Option<Vec<ProofStep>> {
    candidates.into_iter().find(|steps| {
        prove_claim_by_steps(
            source_path,
            function_block,
            parsed_function,
            claim,
            claim_label,
            function_environment,
            predicate_environment,
            click_function_environment,
            resource_environment,
            theorem_environment,
            steps,
        )
        .is_ok()
    })
}

fn frame_proof_step_candidates() -> Vec<Vec<ProofStep>> {
    vec![vec![ProofStep::SymbolicExecute, ProofStep::Frame(None)]]
}

fn bounded_execution_proof_step_candidates(claim: &FunctionClaimRef<'_>) -> Vec<Vec<ProofStep>> {
    match claim {
        FunctionClaimRef::Ensure(_, _) => vec![
            vec![ProofStep::BoundedExecute, ProofStep::Simp],
            vec![ProofStep::BoundedExecute],
        ],
        FunctionClaimRef::Effect(_, _) => {
            vec![vec![ProofStep::BoundedExecute, ProofStep::Frame(None)]]
        }
    }
}

fn auto_loop_verification_proof_step_candidates(
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
) -> Vec<Vec<ProofStep>> {
    let mut base = vec![ProofStep::SymbolicExecute];
    base.extend(
        loop_step_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofStep::LoopVc(CodeRegionRef::Loop(loop_index))),
    );
    base.extend(
        loop_effect_summary_regions(function_block)
            .into_iter()
            .map(|loop_index| ProofStep::Frame(Some(CodeRegionRef::Loop(loop_index)))),
    );

    match claim {
        FunctionClaimRef::Ensure(_, _) => {
            let mut simp = base.clone();
            simp.push(ProofStep::Simp);

            let direct = base;
            vec![simp, direct]
        }
        FunctionClaimRef::Effect(_, _) => {
            let mut frame = base.clone();
            frame.push(ProofStep::Frame(None));

            let direct = base;
            vec![frame, direct]
        }
    }
}

fn loop_step_regions(function_block: &FunctionBlock) -> BTreeSet<usize> {
    function_block
        .structural_clauses()
        .iter()
        .filter_map(|clause| match clause.region() {
            CodeRegion::Loop(index) => Some(*index),
            CodeRegion::Function | CodeRegion::Statement(_) => None,
        })
        .collect()
}

fn loop_effect_summary_regions(function_block: &FunctionBlock) -> BTreeSet<usize> {
    function_block
        .structural_clauses()
        .iter()
        .filter_map(|clause| match clause.region() {
            CodeRegion::Loop(index)
                if clause.items().iter().any(StructuralItem::is_effect_kind) =>
            {
                Some(*index)
            }
            _ => None,
        })
        .collect()
}

fn execution_obligation_error(
    execution: &crate::kernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_propositions: &[Proposition],
) -> Option<ClickError> {
    execution_obligation_error_for_tactic("auto", execution, ensure_label, requirement_propositions)
}

fn execution_obligation_error_for_tactic(
    tactic_name: &str,
    execution: &crate::kernel::SymbolicCExecution,
    ensure_label: &str,
    requirement_propositions: &[Proposition],
) -> Option<ClickError> {
    if let Some(limit) = execution.limit() {
        return Some(ClickError::new(format!(
            "`{tactic_name}` hit execution limit {limit:?} for `{ensure_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Some(ClickError::new(format!(
            "`{tactic_name}` could not prove any complete execution path for `{ensure_label}`"
        )));
    }

    for (path_index, path) in execution.paths().iter().enumerate() {
        if !path.obligations().is_empty() {
            return Some(ClickError::new(format!(
                "`{tactic_name}` failed for `{ensure_label}` path {path_index}: remaining proof obligations: {}\n  available requirements: {}\n  path facts: {}",
                describe_obligations(path.obligations()),
                describe_propositions(&requirement_propositions),
                describe_facts(path.facts())
            )));
        }
    }

    None
}

fn prove_claim_from_execution(
    execution: &crate::kernel::SymbolicCExecution,
    execution_kind: AutoExecutionKind<'_>,
    source_path: &str,
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
    claim_label: &str,
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_propositions: &[Proposition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let proof_kind = execution_kind.proof_kind();
    let tactic_name = execution_kind.tactic_name();
    if let Some(limit) = execution.limit() {
        return Err(ClickError::new(format!(
            "`{tactic_name}` hit execution limit {limit:?} for `{claim_label}`"
        )));
    }
    if execution.paths().is_empty() {
        return Err(ClickError::new(format!(
            "`{tactic_name}` could not prove any complete execution path for `{claim_label}`"
        )));
    }

    let mut verified = Vec::new();
    for (path_index, path) in execution.paths().iter().enumerate() {
        let outcome = match implication_body(path.theorem().proposition()) {
            Proposition::CFunctionExecutes { outcome, .. } => outcome.clone(),
            proposition => {
                return Err(ClickError::new(format!(
                    "`{tactic_name}` failed for `{claim_label}` path {path_index}: unexpected theorem body {proposition:?}\n  available requirements: {}\n  path facts: {}",
                    describe_propositions(&requirement_propositions),
                    describe_facts(path.facts())
                )));
            }
        };

        let mut path_requirements = requirement_propositions.to_vec();
        path_requirements.extend(path.facts().iter().map(|fact| fact.proposition().clone()));
        check_function_claim(
            claim_label,
            path_index,
            path.facts(),
            &path_requirements,
            claim,
            parameters,
            arguments,
            state,
            &outcome,
            predicate_environment,
            click_function_environment,
            &[],
        )?;
        let path_requirements_description = describe_propositions(&path_requirements);
        let specification = c_function_specification(
            state.clone(),
            arguments.to_vec(),
            path_requirements,
            outcome.clone(),
        );
        let theorem = match execution_kind {
            AutoExecutionKind::Frame | AutoExecutionKind::LoopVerification => {
                prove_c_function_satisfies_specification_from_symbolic_path(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    path.facts(),
                    path.obligations(),
                )
            }
            AutoExecutionKind::BoundedExecution { environment } => {
                prove_c_function_satisfies_specification_with_environment(
                    function.clone(),
                    specification.clone(),
                    Assumptions::new(),
                    (*environment).clone(),
                )
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "`auto` failed for `{claim_label}` path {path_index}: execution did not satisfy the packaged specification\n  available requirements: {}\n  path facts: {}",
                        path_requirements_description,
                        describe_facts(path.facts())
                    ))
                })?
            }
        };

        verified.push(VerifiedCTheorem {
            source_path: source_path.to_string(),
            function_block: function_block.clone(),
            claim: claim.verified_claim(),
            proof_kind,
            proof_steps: None,
            specification,
            theorem,
        });
    }

    Ok(verified)
}

fn parse_verified_sources<'a>(
    file: &ClickFile,
    c_sources: &'a BTreeMap<&str, &str>,
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
) -> Result<CFunctionEnvironment, ClickError> {
    let mut environment = CFunctionEnvironment::new();
    for (_, function) in parsed_sources.values() {
        let function = match function_blocks
            .iter()
            .find(|block| block.signature().name() == function.name())
        {
            Some(function_block) => {
                let (resource_requires, resource_ensures) =
                    function_resource_summary(function_block)?;
                function
                    .to_kernel_function()
                    .with_resource_summary(resource_requires, resource_ensures)
            }
            None => function.to_kernel_function(),
        };
        environment = environment.with_function(function);
    }
    Ok(environment)
}

fn function_resource_summary(
    function_block: &FunctionBlock,
) -> Result<(Vec<CResourceSpec>, Vec<CResourceSpec>), ClickError> {
    let requires = function_block
        .requires()
        .iter()
        .filter_map(|requirement| match requirement.inner() {
            Requirement::Resource(resource) => Some(resource_clause_to_resource_spec(resource)),
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
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
        ResourceClause::Free(segment) => Ok(CResourceSpec::Free(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } => Ok(CResourceSpec::Named {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(resource_argument_to_c_expression)
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types
                .iter()
                .map(|c_type| c_type.to_kernel_type())
                .collect(),
        }),
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

fn describe_propositions(propositions: &[Proposition]) -> String {
    if propositions.is_empty() {
        return "[]".to_string();
    }

    format!("{propositions:?}")
}

fn describe_facts(facts: &[PathFact]) -> String {
    if facts.is_empty() {
        return "[]".to_string();
    }

    let entries = facts
        .iter()
        .map(|fact| format!("{:?}", fact.proposition()))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn describe_obligations(obligations: &[ProofObligation]) -> String {
    if obligations.is_empty() {
        return "[]".to_string();
    }

    let entries = obligations
        .iter()
        .map(|obligation| match obligation.context() {
            Some(context) => format!("{context}: {:?}", obligation.proposition()),
            None => format!("{:?}", obligation.proposition()),
        })
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn describe_function_outcome(
    outcome: &CFunctionOutcome,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match outcome {
        CFunctionOutcome::Return { value, .. } => {
            format!(
                "returned {}",
                describe_c_value(value, parameters, arguments)
            )
        }
        CFunctionOutcome::UndefinedBehavior(kind) => match kind {
            crate::kernel::CUndefinedBehavior::SignedOverflow => {
                "undefined behavior: signed overflow".to_string()
            }
            crate::kernel::CUndefinedBehavior::DivisionByZero => {
                "undefined behavior: division by zero".to_string()
            }
            crate::kernel::CUndefinedBehavior::InvalidShift => {
                "undefined behavior: invalid shift".to_string()
            }
            crate::kernel::CUndefinedBehavior::InvalidMemory => {
                "undefined behavior: invalid memory access".to_string()
            }
        },
        CFunctionOutcome::RuntimeError(error) => {
            format!(
                "runtime error: {}",
                describe_runtime_error(error, parameters, arguments)
            )
        }
    }
}

fn describe_runtime_error(
    error: &crate::kernel::CRuntimeError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        crate::kernel::CRuntimeError::UnboundVariable(name) => {
            format!("unbound variable `{name}`")
        }
        crate::kernel::CRuntimeError::UnknownFunction(name) => {
            format!("unknown function `{name}`")
        }
        crate::kernel::CRuntimeError::TypeMismatch => "type mismatch".to_string(),
        crate::kernel::CRuntimeError::WrongArity { expected, actual } => {
            format!("wrong argument count: expected {expected}, got {actual}")
        }
        crate::kernel::CRuntimeError::MissingReturn => "missing return".to_string(),
        crate::kernel::CRuntimeError::MissingResource { resource } => format!(
            "missing resource `{}`",
            describe_resource(resource, parameters, arguments)
        ),
        crate::kernel::CRuntimeError::DuplicateResource { resource } => format!(
            "duplicate affine resource `{}`",
            describe_resource(resource, parameters, arguments)
        ),
    }
}

fn describe_resources(
    resources: &[CResource],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if resources.is_empty() {
        return "[]".to_string();
    }
    let entries = resources
        .iter()
        .map(|resource| describe_resource(resource, parameters, arguments))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn describe_resource(
    resource: &CResource,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    let (name, range) = match resource {
        CResource::Read(range) => ("read", range),
        CResource::Write(range) => ("write", range),
        CResource::Free(range) => ("free", range),
        CResource::Named {
            name,
            arguments: resource_arguments,
        } => {
            return format!(
                "{name}({})",
                resource_arguments
                    .iter()
                    .map(|argument| describe_c_value(argument, parameters, arguments))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }
    };
    format!(
        "{name}({})",
        describe_memory_range(range, parameters, arguments)
    )
}

fn describe_memory_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(description) = describe_parameter_relative_range(range, parameters, arguments) {
        return description;
    }
    format!(
        "{}[{}..{}]",
        describe_pointer(range.base(), parameters, arguments),
        describe_bitvector(range.start()),
        describe_bitvector(range.end())
    )
}

fn describe_parameter_relative_range(
    range: &CMemoryRange,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(base_index) = diagnostic_pointer_element_index_from_base(
            range.base(),
            base,
            diagnostic_parameter_element_width(parameter),
        ) else {
            continue;
        };
        let start = bitvector32_add(base_index.clone(), range.start().clone());
        let end = bitvector32_add(base_index, range.end().clone());
        return Some(format!(
            "{}[{}..{}]",
            parameter.name(),
            describe_bitvector(&start),
            describe_bitvector(&end)
        ));
    }
    None
}

fn describe_pointer(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let CExpression::Value(CValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(index) = diagnostic_pointer_element_index_from_base(
            pointer,
            base,
            diagnostic_parameter_element_width(parameter),
        ) {
            if index == Bitvector32Term::Constant(0) {
                return parameter.name().to_string();
            }
            return format!("{}[{}]", parameter.name(), describe_bitvector(&index));
        }
    }
    format!(
        "{}@{}",
        pointer.block,
        describe_pointer_offset(&pointer.offset)
    )
}

fn diagnostic_parameter_element_width(parameter: &syntax::C0Parameter) -> i64 {
    match parameter.c_type() {
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => 1,
        C0Type::Int32 | C0Type::UInt8 | C0Type::Int32Pointer | C0Type::Int32Array(_) => 4,
    }
}

fn diagnostic_pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: i64,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width),
                diagnostic_element_index_from_pointer_offset(&base.offset, byte_width),
            ) {
                Some(bitvector32_subtract(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

fn diagnostic_element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
    byte_width: i64,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % byte_width == 0 => {
            let index = offset / byte_width;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: actual_width,
        } if *actual_width == byte_width => Some(value.as_ref().clone()),
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            diagnostic_element_index_from_pointer_offset(left, byte_width)?,
            diagnostic_element_index_from_pointer_offset(right, byte_width)?,
        )),
        _ => None,
    }
}

fn describe_c_value(
    value: &CValue,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match value {
        CValue::Int32(value) => describe_bitvector_with_context(value, parameters, arguments),
        CValue::UInt8(value) => {
            format!(
                "{}u8",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        CValue::Pointer(pointer) => describe_pointer(pointer, parameters, arguments),
    }
}

fn describe_contract_segment(segment: &ContractSegment) -> String {
    let prefix = match segment.state {
        ContractSegmentState::Current => "",
        ContractSegmentState::Old => "old ",
    };
    format!(
        "{}{}[{}..{}]",
        prefix,
        describe_c_expression(&segment.base),
        describe_c_expression(&segment.start),
        describe_c_expression(&segment.end)
    )
}

fn describe_evaluated_segments(segments: &[EvaluatedContractSegment]) -> String {
    if segments.is_empty() {
        return "[]".to_string();
    }
    let entries = segments
        .iter()
        .map(|segment| {
            format!(
                "{} => {}[{}..{}]",
                describe_contract_segment(&segment.source),
                describe_pointer(&segment.base, &[], &[]),
                describe_bitvector(&segment.start),
                describe_bitvector(&segment.end)
            )
        })
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn describe_contract_segments(segments: &[EvaluatedContractSegment]) -> String {
    if segments.is_empty() {
        return "[]".to_string();
    }
    let entries = segments
        .iter()
        .map(|segment| describe_contract_segment(&segment.source))
        .collect::<Vec<_>>();
    format!("[{}]", entries.join(", "))
}

fn describe_c_expression(expression: &CExpression) -> String {
    match expression {
        CExpression::Value(value) => describe_c_value(value, &[], &[]),
        CExpression::Variable(name) => name.clone(),
        CExpression::AddressOf(target) => format!("&{}", describe_c_expression(target)),
        CExpression::LessThan(left, right) => describe_binary_c_expression(left, "<", right),
        CExpression::LessEqual(left, right) => describe_binary_c_expression(left, "<=", right),
        CExpression::GreaterThan(left, right) => describe_binary_c_expression(left, ">", right),
        CExpression::GreaterEqual(left, right) => describe_binary_c_expression(left, ">=", right),
        CExpression::Equal(left, right) => describe_binary_c_expression(left, "==", right),
        CExpression::NotEqual(left, right) => describe_binary_c_expression(left, "!=", right),
        CExpression::Not(expression) => format!("!{}", describe_c_expression(expression)),
        CExpression::And(left, right) => describe_binary_c_expression(left, "&&", right),
        CExpression::Or(left, right) => describe_binary_c_expression(left, "||", right),
        CExpression::Add(left, right) => describe_binary_c_expression(left, "+", right),
        CExpression::Subtract(left, right) => describe_binary_c_expression(left, "-", right),
        CExpression::Multiply(left, right) => describe_binary_c_expression(left, "*", right),
        CExpression::Divide(left, right) => describe_binary_c_expression(left, "/", right),
        CExpression::Remainder(left, right) => describe_binary_c_expression(left, "%", right),
        CExpression::ShiftLeft(left, right) => describe_binary_c_expression(left, "<<", right),
        CExpression::ShiftRight(left, right) => describe_binary_c_expression(left, ">>", right),
        CExpression::BitwiseAnd(left, right) => describe_binary_c_expression(left, "&", right),
        CExpression::BitwiseOr(left, right) => describe_binary_c_expression(left, "|", right),
        CExpression::BitwiseXor(left, right) => describe_binary_c_expression(left, "^", right),
        CExpression::BitwiseNot(expression) => format!("~{}", describe_c_expression(expression)),
        CExpression::Load(pointer) => format!("*{}", describe_c_expression(pointer)),
        CExpression::Index(base, index) => {
            format!(
                "{}[{}]",
                describe_c_expression(base),
                describe_c_expression(index)
            )
        }
    }
}

fn describe_binary_c_expression(left: &CExpression, operator: &str, right: &CExpression) -> String {
    format!(
        "({} {operator} {})",
        describe_c_expression(left),
        describe_c_expression(right)
    )
}

fn describe_contract_expression(expression: &ContractExpression) -> String {
    match expression {
        ContractExpression::CFragment(expression) => describe_c_expression(expression),
        ContractExpression::Old(expression) => {
            format!("old({})", describe_contract_expression(expression))
        }
        ContractExpression::At {
            selector,
            expression,
        } => format!(
            "at({}, {})",
            describe_visit_selector(selector),
            describe_contract_expression(expression)
        ),
        ContractExpression::Add(left, right) => {
            describe_binary_contract_expression(left, "+", right)
        }
        ContractExpression::Subtract(left, right) => {
            describe_binary_contract_expression(left, "-", right)
        }
        ContractExpression::Multiply(left, right) => {
            describe_binary_contract_expression(left, "*", right)
        }
        ContractExpression::Divide(left, right) => {
            describe_binary_contract_expression(left, "/", right)
        }
        ContractExpression::Remainder(left, right) => {
            describe_binary_contract_expression(left, "%", right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            describe_binary_contract_expression(left, "<<", right)
        }
        ContractExpression::ShiftRight(left, right) => {
            describe_binary_contract_expression(left, ">>", right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            describe_binary_contract_expression(left, "&", right)
        }
        ContractExpression::BitwiseOr(left, right) => {
            describe_binary_contract_expression(left, "|", right)
        }
        ContractExpression::BitwiseXor(left, right) => {
            describe_binary_contract_expression(left, "^", right)
        }
        ContractExpression::BitwiseNot(expression) => {
            format!("~{}", describe_contract_expression(expression))
        }
        ContractExpression::Index(base, index) => format!(
            "{}[{}]",
            describe_contract_expression(base),
            describe_contract_expression(index)
        ),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => format!(
            "if {} then {} else {}",
            describe_click_proposition(condition),
            describe_contract_expression(then_branch),
            describe_contract_expression(else_branch)
        ),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => format!(
            "fold({}..{}, {}, ({accumulator}, {item}) => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_contract_expression(initial),
            describe_contract_expression(body)
        ),
        ContractExpression::Let {
            name, value, body, ..
        } => format!(
            "let {name} = {}; {}",
            describe_contract_expression(value),
            describe_contract_expression(body)
        ),
        ContractExpression::Call { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn describe_binary_contract_expression(
    left: &ContractExpression,
    operator: &str,
    right: &ContractExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_contract_expression(left),
        describe_contract_expression(right)
    )
}

fn describe_click_proposition(proposition: &ClickProposition) -> String {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => format!(
            "{} {operator} {}",
            describe_contract_expression(left),
            describe_contract_expression(right)
        ),
        ClickProposition::And(left, right) => describe_binary_click_proposition(left, "&&", right),
        ClickProposition::Or(left, right) => describe_binary_click_proposition(left, "||", right),
        ClickProposition::Not(proposition) => {
            format!("!{}", describe_click_proposition(proposition))
        }
        ClickProposition::Implies(left, right) => {
            describe_binary_click_proposition(left, "=>", right)
        }
        ClickProposition::ForAll { c_type, name, body } => format!(
            "forall ({c_type:?} {name}) {{ {} }}",
            describe_click_proposition(body)
        ),
        ClickProposition::Exists { c_type, name, body } => format!(
            "exists ({c_type:?} {name}) {{ {} }}",
            describe_click_proposition(body)
        ),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => format!(
            "({}..{}).all({item} => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_click_proposition(body)
        ),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => format!(
            "({}..{}).any({item} => {})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_click_proposition(body)
        ),
        ClickProposition::PredicateCall { name, arguments } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn describe_binary_click_proposition(
    left: &ClickProposition,
    operator: &str,
    right: &ClickProposition,
) -> String {
    format!(
        "({} {operator} {})",
        describe_click_proposition(left),
        describe_click_proposition(right)
    )
}

fn describe_visit_selector(selector: &VisitSelector) -> String {
    match selector {
        VisitSelector::ProgramPoint(point) => describe_program_point_ref(point),
    }
}

fn describe_program_point_ref(point: &ProgramPointRef) -> String {
    let kind = match point.kind {
        ProgramPointKind::Entry => "entry",
    };
    format!("{}.{}", describe_code_region_ref(&point.region), kind)
}

fn describe_code_region_ref(region: &CodeRegionRef) -> String {
    match region {
        CodeRegionRef::Function => "function".to_string(),
        CodeRegionRef::Loop(index) => format!("loop({index})"),
        CodeRegionRef::Statement(index) => format!("statement({index})"),
        CodeRegionRef::Label(name) => name.clone(),
    }
}

fn describe_bitvector(term: &Bitvector32Term) -> String {
    describe_bitvector_with_context(term, &[], &[])
}

fn describe_bitvector_with_context(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return name;
    }
    match term {
        Bitvector32Term::Constant(value) => format!("{}", *value as i32),
        Bitvector32Term::Variable(variable) => format!("v{}", variable.0),
        Bitvector32Term::Add(left, right) => {
            describe_binary_bitvector_with_context(left, "+", right, parameters, arguments)
        }
        Bitvector32Term::Subtract(left, right) => {
            describe_binary_bitvector_with_context(left, "-", right, parameters, arguments)
        }
        Bitvector32Term::Multiply(left, right) => {
            describe_binary_bitvector_with_context(left, "*", right, parameters, arguments)
        }
        Bitvector32Term::Divide(left, right) => {
            describe_binary_bitvector_with_context(left, "/", right, parameters, arguments)
        }
        Bitvector32Term::Remainder(left, right) => {
            describe_binary_bitvector_with_context(left, "%", right, parameters, arguments)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            describe_binary_bitvector_with_context(left, "<<", right, parameters, arguments)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            describe_binary_bitvector_with_context(left, ">>", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            describe_binary_bitvector_with_context(left, "&", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            describe_binary_bitvector_with_context(left, "|", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            describe_binary_bitvector_with_context(left, "^", right, parameters, arguments)
        }
        Bitvector32Term::BitwiseNot(value) => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameters, arguments)
            )
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => format!(
            "if {} then {} else {}",
            describe_condition(condition),
            describe_bitvector_with_context(then_term, parameters, arguments),
            describe_bitvector_with_context(else_term, parameters, arguments)
        ),
        Bitvector32Term::RangeFold { .. } => format!("{term:?}"),
        Bitvector32Term::MemoryLoad(_, pointer) => {
            format!("load({})", describe_pointer(pointer, parameters, arguments))
        }
    }
}

fn describe_parameter_bitvector(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<String> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        match argument {
            CExpression::Value(CValue::Int32(value))
                if value == term && parameter.c_type() == C0Type::Int32 =>
            {
                return Some(parameter.name().to_string());
            }
            CExpression::Value(CValue::UInt8(value))
                if value == term && parameter.c_type() == C0Type::UInt8 =>
            {
                return Some(parameter.name().to_string());
            }
            _ => {}
        }
    }
    None
}

fn describe_binary_bitvector_with_context(
    left: &Bitvector32Term,
    operator: &str,
    right: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    format!(
        "({} {operator} {})",
        describe_bitvector_with_context(left, parameters, arguments),
        describe_bitvector_with_context(right, parameters, arguments)
    )
}

fn describe_pointer_offset(offset: &PointerOffsetTerm) -> String {
    match offset {
        PointerOffsetTerm::Constant(value) => value.to_string(),
        PointerOffsetTerm::Variable(variable) => format!("off{}", variable.0),
        PointerOffsetTerm::Add(left, right) => format!(
            "({} + {})",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            format!("{} * {byte_width}", describe_bitvector(value))
        }
    }
}

fn describe_condition(condition: &ConditionTerm) -> String {
    match condition {
        ConditionTerm::Constant(value) => value.to_string(),
        ConditionTerm::Variable(variable) => format!("cond{}", variable.0),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            describe_binary_condition(left, "<", right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            describe_binary_condition(left, "<=", right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            describe_binary_condition(left, ">", right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            describe_binary_condition(left, ">=", right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            describe_binary_condition(left, "==", right)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            format!(
                "overflow({} + {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            format!(
                "overflow({} - {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            format!(
                "overflow({} * {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            format!(
                "overflow({} / {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            format!(
                "overflow({} << {})",
                describe_bitvector(left),
                describe_bitvector(right)
            )
        }
        ConditionTerm::PointerOffsetEqual(left, right) => format!(
            "{} == {}",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
    }
}

fn describe_binary_condition(
    left: &Bitvector32Term,
    operator: &str,
    right: &Bitvector32Term,
) -> String {
    format!(
        "{} {operator} {}",
        describe_bitvector(left),
        describe_bitvector(right)
    )
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
        if expected.c_type() != actual.c_type() || expected.name() != actual.name() {
            return Err(ClickError::new(format!(
                "signature mismatch for `{}` parameter {} in `{source_path}`: .click has {:?} {}, C has {:?} {}",
                signature.name(),
                index + 1,
                expected.c_type(),
                expected.name(),
                actual.c_type(),
                actual.name()
            )));
        }
    }

    Ok(())
}

fn validate_structural_clauses(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    let statement_count = count_statements(parsed_function.body());
    for structural_clause in function_block.structural_clauses() {
        match structural_clause.region() {
            CodeRegion::Function => {
                return Err(ClickError::new(
                    "`for function` structural proof blocks are not supported",
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
                for item in structural_clause.items() {
                    if item.kind() == StructuralItemKind::Invariant {
                        return Err(ClickError::new(
                            "`invariant` is only supported at loop code regions",
                        ));
                    }
                    if item.is_effect_kind() {
                        return Err(ClickError::new(
                            "`immutable` and `mutable` are only supported at loop code regions inside structural proof blocks",
                        ));
                    }
                }
            }
            CodeRegion::Loop(_) => {}
        }

        for item in structural_clause.items() {
            if item.is_effect_kind() {
                if !item.proof().is_auto_or_frame_tactic() {
                    return Err(ClickError::new(
                        "`immutable` and `mutable` structural clauses must use the default prover, `by auto;`, or `by frame;`",
                    ));
                }
            } else if item.kind() == StructuralItemKind::Invariant {
                if !item.proof().is_auto_tactic() && !item.proof().is_unfold_only_steps() {
                    return Err(ClickError::new(
                        "`invariant` structural clauses must use the default prover, `by auto;`, or an unfold-only proof-step script such as `by { unfold(sorted_range); }` in this first slice",
                    ));
                }
            } else if !item.proof().is_auto_tactic() {
                return Err(ClickError::new(
                    "`assert` structural clauses must use the default prover or `by auto;` in this first slice",
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

fn annotated_function(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    entry_state: &CState,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CFunction, ClickError> {
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        predicate_environment,
        click_function_environment,
        entry_state,
        entry_values: parameter_values(parsed_function.parameters(), arguments)?,
        parameter_array_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_000_000,
    };
    let body = lowerer.lower_statement(parsed_function.body())?;
    let (resource_requires, resource_ensures) = function_resource_summary(function_block)?;
    Ok(c_function(
        parsed_function.return_type().to_kernel_type(),
        parsed_function.name().to_string(),
        parsed_function
            .parameters()
            .iter()
            .map(syntax::C0Parameter::to_kernel_parameter)
            .collect(),
        body,
    )
    .with_resource_summary(resource_requires, resource_ensures))
}

struct AnnotationLowerer<'a> {
    structural_clauses: &'a [StructuralClause],
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    entry_state: &'a CState,
    entry_values: BTreeMap<String, CValue>,
    parameter_array_element_types: BTreeMap<String, CType>,
    quantified_values: BTreeMap<String, CValue>,
    loop_index: usize,
    statement_index: usize,
    next_quantifier_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LabeledCheck {
    condition: CExpression,
    label: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResolvedProgramPoint {
    FunctionEntry,
    LoopEntry(usize),
}

impl AnnotationLowerer<'_> {
    fn lower_statement(
        &mut self,
        statement: &syntax::C0Statement,
    ) -> Result<CStatement, ClickError> {
        Ok(match statement {
            syntax::C0Statement::Seq(first, second) => {
                c_seq(self.lower_statement(first)?, self.lower_statement(second)?)
            }
            syntax::C0Statement::While { condition, body } => {
                let statement_index = self.next_statement_index();
                let loop_index = self.next_loop_index();
                let lowered_body = self.lower_statement(body)?;
                let loop_asserts = self.loop_assert_checks(loop_index);
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_effect_checks(loop_index, body)?;
                let lowered_loop = c_while_with_invariant_and_effect_checks(
                    condition.to_kernel_expression(),
                    Vec::new(),
                    invariant_checks,
                    effect_checks,
                    lowered_body,
                );
                let lowered_loop = prepend_labeled_asserts(lowered_loop, &loop_asserts);
                self.prepend_statement_asserts(statement_index, lowered_loop)
            }
            statement => {
                let statement_index = self.next_statement_index();
                let lowered = statement.to_kernel_statement();
                self.prepend_statement_asserts(statement_index, lowered)
            }
        })
    }

    fn next_statement_index(&mut self) -> usize {
        let index = self.statement_index;
        self.statement_index += 1;
        index
    }

    fn next_loop_index(&mut self) -> usize {
        let index = self.loop_index;
        self.loop_index += 1;
        index
    }

    fn prepend_statement_asserts(
        &self,
        statement_index: usize,
        statement: CStatement,
    ) -> CStatement {
        let checks = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Statement(statement_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Assert)
            .enumerate()
            .map(|(item_index, item)| LabeledCheck {
                condition: click_proposition_to_c_expression(
                    item.proposition()
                        .expect("assert structural item should contain a proposition"),
                )
                .expect("structural propositions should be validated before lowering"),
                label: format!(
                    "statement {statement_index} {} {item_index}",
                    structural_item_kind_label(item.kind())
                ),
            })
            .collect::<Vec<_>>();
        prepend_labeled_asserts(statement, &checks)
    }

    fn loop_invariant_checks(
        &mut self,
        loop_index: usize,
    ) -> Result<Vec<CLoopInvariantCheck>, ClickError> {
        self.structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .enumerate()
            .map(|(item_index, item)| {
                let proposition = unfold_structural_invariant_proposition(
                    self.predicate_environment,
                    item.proposition()
                        .expect("invariant structural item should contain a proposition"),
                    item.proof(),
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "loop {loop_index} invariant {item_index}: {message}"
                    ))
                })?;
                Ok(CLoopInvariantCheck::new(
                    self.click_proposition_to_spec_proposition(
                        &proposition,
                        &SpecElaborationContext::for_loop_invariant(loop_index),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "loop {loop_index} invariant {item_index}: {message}"
                        ))
                    })?,
                    Some(format!("loop {loop_index} invariant {item_index} entry")),
                    Some(format!(
                        "loop {loop_index} invariant {item_index} preservation"
                    )),
                ))
            })
            .collect()
    }

    fn click_proposition_to_spec_proposition(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => Ok(SpecProposition::Comparison {
                left: self.lower_contract_expression_to_spec(left, environment)?,
                operator: c_comparison_operator(*operator),
                right: self.lower_contract_expression_to_spec(right, environment)?,
            }),
            ClickProposition::And(left, right) => Ok(SpecProposition::And(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::Or(left, right) => Ok(SpecProposition::Or(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::Not(body) => Ok(SpecProposition::Not(Box::new(
                self.click_proposition_to_spec_proposition(body, environment)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(SpecProposition::Implies(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err("only `forall (int32 ...)` is supported".to_string());
                }
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable))),
                );
                let previous = self.quantified_values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                Ok(SpecProposition::ForAllInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                })
            }
            ClickProposition::Exists { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err("only `exists (int32 ...)` is supported".to_string());
                }
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable))),
                );
                let previous = self.quantified_values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                Ok(SpecProposition::ExistsInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                })
            }
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => {
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let item_value =
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(
                    item.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(item.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(item);
                    }
                }
                let range = spec_range_membership_proposition(start, item_value, end);
                Ok(SpecProposition::ForAllInt32 {
                    name: item.clone(),
                    variable,
                    body: Box::new(SpecProposition::Implies(Box::new(range), Box::new(body))),
                })
            }
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => {
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let item_value =
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(
                    item.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(item.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(item);
                    }
                }
                let range = spec_range_membership_proposition(start, item_value, end);
                Ok(SpecProposition::ExistsInt32 {
                    name: item.clone(),
                    variable,
                    body: Box::new(SpecProposition::And(Box::new(range), Box::new(body))),
                })
            }
            ClickProposition::PredicateCall { name, arguments } => Ok(SpecProposition::Predicate {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.lower_contract_expression_to_spec(argument, environment))
                    .collect::<Result<Vec<_>, _>>()?,
            }),
        }
    }

    fn lower_contract_expression_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            ContractExpression::CFragment(expression) => {
                self.lower_c_fragment_to_spec(expression, environment)
            }
            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_expression_to_spec(selector, expression, environment),
            ContractExpression::Add(left, right) => Ok(SpecExpression::Add(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Subtract(left, right) => Ok(SpecExpression::Subtract(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_contract_expression_to_spec(expression, environment)?,
            ))),
            ContractExpression::Index(base, index) => {
                let array_ref = self.lower_array_ref_to_spec(base, environment)?;
                let index = self.lower_contract_expression_to_spec(index, environment)?;
                Ok(SpecExpression::MemoryLoad {
                    memory: array_ref.memory,
                    pointer: Box::new(SpecExpression::PointerOffset {
                        pointer: Box::new(array_ref.pointer),
                        elements: Box::new(index),
                        byte_width: array_ref.element_type.byte_width(),
                    }),
                    value_type: array_ref.element_type,
                })
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => Ok(SpecExpression::If {
                condition: Box::new(
                    self.click_proposition_to_spec_proposition(condition, environment)?,
                ),
                then_branch: Box::new(
                    self.lower_contract_expression_to_spec(then_branch, environment)?,
                ),
                else_branch: Box::new(
                    self.lower_contract_expression_to_spec(else_branch, environment)?,
                ),
            }),
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    accumulator.clone(),
                    SpecExpression::CExpression(CExpression::Variable(accumulator.clone())),
                );
                body_environment.values.insert(
                    item.clone(),
                    SpecExpression::CExpression(CExpression::Variable(item.clone())),
                );
                Ok(SpecExpression::RangeFold {
                    start: Box::new(self.lower_contract_expression_to_spec(start, environment)?),
                    end: Box::new(self.lower_contract_expression_to_spec(end, environment)?),
                    initial: Box::new(
                        self.lower_contract_expression_to_spec(initial, environment)?,
                    ),
                    accumulator: accumulator.clone(),
                    item: item.clone(),
                    body: Box::new(
                        self.lower_contract_expression_to_spec(body, &body_environment)?,
                    ),
                })
            }
            ContractExpression::Let {
                name, value, body, ..
            } => {
                let value = self.lower_contract_expression_to_spec(value, environment)?;
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::CExpression(CExpression::Variable(name.clone())),
                );
                Ok(SpecExpression::Let {
                    name: name.clone(),
                    value: Box::new(value),
                    body: Box::new(
                        self.lower_contract_expression_to_spec(body, &body_environment)?,
                    ),
                })
            }
            ContractExpression::Call { name, arguments } => {
                self.lower_click_function_call_to_spec(name, arguments, environment)
            }
        }
    }

    fn lower_at_expression_to_spec(
        &mut self,
        selector: &VisitSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match self.resolve_visit_selector(selector)? {
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                Ok(SpecExpression::LoopEntrySnapshot(Box::new(
                    self.lower_contract_expression_to_spec(expression, environment)?,
                )))
            }
        }
    }

    fn resolve_visit_selector(
        &self,
        selector: &VisitSelector,
    ) -> Result<ResolvedProgramPoint, String> {
        match selector {
            VisitSelector::ProgramPoint(program_point) => {
                self.resolve_program_point_ref(program_point)
            }
        }
    }

    fn resolve_program_point_ref(
        &self,
        program_point: &ProgramPointRef,
    ) -> Result<ResolvedProgramPoint, String> {
        let region = self.resolve_code_region_ref(&program_point.region)?;
        match (region, program_point.kind) {
            (CodeRegion::Function, ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::FunctionEntry)
            }
            (CodeRegion::Loop(index), ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::LoopEntry(index))
            }
            (CodeRegion::Statement(index), ProgramPointKind::Entry) => Err(format!(
                "`at(statement({index}).entry, ...)` is not supported yet"
            )),
        }
    }

    fn resolve_code_region_ref(&self, region_ref: &CodeRegionRef) -> Result<CodeRegion, String> {
        match region_ref {
            CodeRegionRef::Function => Ok(CodeRegion::Function),
            CodeRegionRef::Loop(index) => Ok(CodeRegion::Loop(*index)),
            CodeRegionRef::Statement(index) => Ok(CodeRegion::Statement(*index)),
            CodeRegionRef::Label(label) => self
                .structural_clauses
                .iter()
                .find(|clause| clause.label() == Some(label.as_str()))
                .map(|clause| *clause.region())
                .ok_or_else(|| format!("unknown code region label `{label}`")),
        }
    }

    fn lower_c_fragment_to_spec(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(SpecExpression::Value(value.clone())),
            CExpression::Variable(name) => match environment.values.get(name) {
                Some(value) => Ok(value.clone()),
                None if matches!(environment.current_memory, SpecMemory::Fixed(_)) => {
                    if name == "result" {
                        Err("`result` is not available inside `old(...)`".to_string())
                    } else {
                        Err(format!("unknown old-state variable `{name}`"))
                    }
                }
                None => Ok(SpecExpression::CExpression(CExpression::Variable(
                    name.clone(),
                ))),
            },
            CExpression::Add(left, right) => Ok(SpecExpression::Add(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Subtract(left, right) => Ok(SpecExpression::Subtract(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_c_fragment_to_spec(expression, environment)?,
            ))),
            CExpression::Index(base, index) => {
                let element_type = self
                    .c_expression_array_element_type(base, environment)
                    .unwrap_or(CType::Int32);
                let pointer = SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(base, environment)?),
                    elements: Box::new(self.lower_c_fragment_to_spec(index, environment)?),
                    byte_width: element_type.byte_width(),
                };
                Ok(SpecExpression::MemoryLoad {
                    memory: environment.current_memory.clone(),
                    pointer: Box::new(pointer),
                    value_type: element_type,
                })
            }
            expression => Ok(SpecExpression::CExpression(expression.clone())),
        }
    }

    fn lower_click_function_call_to_spec(
        &mut self,
        name: &str,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let definition = self
            .click_function_environment
            .get(name)
            .ok_or_else(|| format!("unknown function `{name}`"))?;
        if arguments.len() != definition.parameters().len() {
            return Err(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                arguments.len()
            ));
        }

        let mut function_environment =
            SpecElaborationContext::with_current_memory(environment.current_memory.clone());
        for (parameter, argument) in definition.parameters().iter().zip(arguments) {
            if parameter_is_click_array_ref(parameter) {
                let expected_element_type = click_array_element_type(parameter.c_type())
                    .ok_or_else(|| {
                        format!(
                            "function `{}` parameter `{}` is not an array-ref parameter",
                            definition.name(),
                            parameter.name()
                        )
                    })?;
                let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                if array_ref.element_type != expected_element_type {
                    return Err(format!(
                        "function `{}` parameter `{}` expects {:?} array elements, got {:?}",
                        definition.name(),
                        parameter.name(),
                        expected_element_type,
                        array_ref.element_type
                    ));
                }
                function_environment
                    .array_refs
                    .insert(parameter.name().to_string(), array_ref);
            } else {
                function_environment.values.insert(
                    parameter.name().to_string(),
                    self.lower_contract_expression_to_spec(argument, environment)?,
                );
            }
        }

        self.lower_contract_expression_to_spec(definition.body(), &function_environment)
    }

    fn lower_array_ref_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        match expression {
            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_array_ref_to_spec(selector, expression, environment),
            ContractExpression::CFragment(CExpression::Variable(name)) => {
                if let Some(array_ref) = environment.array_refs.get(name) {
                    return Ok(array_ref.clone());
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_c_fragment_to_spec(
                        &CExpression::Variable(name.clone()),
                        environment,
                    )?,
                    element_type: self.array_ref_element_type_for_name(name),
                })
            }
            ContractExpression::Add(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                if let Ok(array_ref) = self.lower_array_ref_to_spec(right, environment) {
                    let offset = self.lower_contract_expression_to_spec(left, environment)?;
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            ContractExpression::Subtract(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let negative_offset = SpecExpression::Subtract(
                        Box::new(SpecExpression::Value(CValue::Int32(
                            Bitvector32Term::Constant(0),
                        ))),
                        Box::new(offset),
                    );
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(negative_offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            _ => Ok(SpecArrayRef {
                memory: environment.current_memory.clone(),
                pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                element_type: self.contract_array_element_type(expression, environment),
            }),
        }
    }

    fn lower_at_array_ref_to_spec(
        &mut self,
        selector: &VisitSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        match self.resolve_visit_selector(selector)? {
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                let SpecArrayRef {
                    memory,
                    pointer,
                    element_type,
                } = self.lower_array_ref_to_spec(expression, environment)?;
                let memory = match memory {
                    SpecMemory::Current => SpecMemory::LoopEntry,
                    memory => memory,
                };
                Ok(SpecArrayRef {
                    memory,
                    pointer: SpecExpression::LoopEntrySnapshot(Box::new(pointer)),
                    element_type,
                })
            }
        }
    }

    fn array_ref_element_type_for_name(&self, name: &str) -> CType {
        self.parameter_array_element_types
            .get(name)
            .copied()
            .unwrap_or(CType::Int32)
    }

    fn contract_array_element_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> CType {
        match expression {
            ContractExpression::CFragment(CExpression::Variable(name)) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .unwrap_or_else(|| self.array_ref_element_type_for_name(name)),
            ContractExpression::At { expression, .. } => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Old(expression) => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Add(left, right) => {
                let left_type = self.contract_array_element_type(left, environment);
                if left_type != CType::Int32 {
                    return left_type;
                }
                self.contract_array_element_type(right, environment)
            }
            ContractExpression::Subtract(left, _) => {
                self.contract_array_element_type(left, environment)
            }
            _ => CType::Int32,
        }
    }

    fn c_expression_array_element_type(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Option<CType> {
        match expression {
            CExpression::Variable(name) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .or_else(|| self.parameter_array_element_types.get(name).copied()),
            CExpression::Add(left, right) => self
                .c_expression_array_element_type(left, environment)
                .or_else(|| self.c_expression_array_element_type(right, environment)),
            CExpression::Subtract(left, _) => {
                self.c_expression_array_element_type(left, environment)
            }
            _ => None,
        }
    }

    fn lower_current_invariant_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(CExpression::Value(value.clone())),
            CExpression::Variable(name) => Ok(self
                .quantified_values
                .get(name)
                .cloned()
                .map(CExpression::Value)
                .unwrap_or_else(|| CExpression::Variable(name.clone()))),
            CExpression::Add(left, right) => Ok(CExpression::Add(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Divide(left, right) => Ok(CExpression::Divide(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
                self.lower_current_invariant_c_expression(expression)?,
            ))),
            CExpression::Index(base, index) => Ok(CExpression::Index(
                Box::new(self.lower_current_invariant_c_expression(base)?),
                Box::new(self.lower_current_invariant_c_expression(index)?),
            )),
            expression => Err(format!(
                "unsupported expression in loop invariant: `{expression:?}`"
            )),
        }
    }

    fn loop_assert_checks(&self, loop_index: usize) -> Vec<LabeledCheck> {
        self.structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Assert)
            .enumerate()
            .map(|(item_index, item)| LabeledCheck {
                condition: click_proposition_to_c_expression(
                    item.proposition()
                        .expect("assert structural item should contain a proposition"),
                )
                .expect("structural propositions should be validated before lowering"),
                label: format!("loop {loop_index} assert {item_index}"),
            })
            .collect()
    }

    fn loop_effect_checks(
        &self,
        loop_index: usize,
        body: &syntax::C0Statement,
    ) -> Result<Vec<CLoopEffectCheck>, ClickError> {
        let modified_locals = c0_loop_modified_locals(body);
        self.structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.is_effect_kind())
            .enumerate()
            .map(|(item_index, item)| {
                let effect = item
                    .effect()
                    .expect("effect structural item should contain an effect");
                let span = match item.kind() {
                    StructuralItemKind::Effect => CLoopEffectSpan::Whole,
                    StructuralItemKind::StepEffect => CLoopEffectSpan::Step,
                    _ => unreachable!("loop effect filter should only include effect items"),
                };
                let lowered = self
                    .lower_loop_effect(effect, span, &modified_locals)
                    .map_err(|message| {
                        ClickError::new(format!("loop {loop_index} effect {item_index}: {message}"))
                    })?;
                let context = match effect {
                    Effect::Immutable => match span {
                        CLoopEffectSpan::Whole => {
                            format!("loop {loop_index} immutable {item_index}")
                        }
                        CLoopEffectSpan::Step => {
                            format!("loop {loop_index} step immutable {item_index}")
                        }
                    },
                    Effect::Mutable(_) => match span {
                        CLoopEffectSpan::Whole => {
                            format!("loop {loop_index} mutable {item_index}")
                        }
                        CLoopEffectSpan::Step => {
                            format!("loop {loop_index} step mutable {item_index}")
                        }
                    },
                };
                Ok(CLoopEffectCheck::new_with_span(
                    lowered,
                    span,
                    Some(context),
                ))
            })
            .collect()
    }

    fn lower_loop_effect(
        &self,
        effect: &Effect,
        span: CLoopEffectSpan,
        modified_locals: &BTreeSet<String>,
    ) -> Result<CLoopEffect, String> {
        match effect {
            Effect::Immutable => Ok(CLoopEffect::Immutable),
            Effect::Mutable(segments) => segments
                .iter()
                .map(|segment| {
                    if segment.state != ContractSegmentState::Current {
                        return Err(
                            "`mutable` inside `loop` expects current-state segments; `old(...)` is not supported here"
                                .to_string(),
                        );
                    }
                    if span == CLoopEffectSpan::Whole {
                        let names = contract_segment_referenced_names(segment);
                        if let Some(name) = names.iter().find(|name| modified_locals.contains(*name))
                        {
                            return Err(format!(
                                "whole-loop `mutable` segment references loop-modified local `{name}`; use `step {{ ... }}` for iteration-relative effects or state a stable whole-loop range"
                            ));
                        }
                    }
                    Ok(CMemorySegment::new(
                        self.lower_current_invariant_c_expression(&segment.base)?,
                        self.lower_current_invariant_c_expression(&segment.start)?,
                        self.lower_current_invariant_c_expression(&segment.end)?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()
                .map(CLoopEffect::Mutable),
        }
    }
}

fn unfold_structural_invariant_proposition(
    predicate_environment: &PredicateEnvironment,
    proposition: &ClickProposition,
    proof: &Proof,
) -> Result<ClickProposition, String> {
    let unfolded_predicates = proof.unfold_step_names();
    if unfolded_predicates.is_empty() {
        return Ok(proposition.clone());
    }

    for name in &unfolded_predicates {
        if predicate_environment.get(name).is_none() {
            return Err(format!("unknown predicate `{name}`"));
        }
    }

    let mut active = BTreeSet::new();
    unfold_click_predicates_in_proposition_with_active(
        predicate_environment,
        &unfolded_predicates,
        proposition,
        &mut active,
    )
}

fn unfold_click_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    unfolded_predicates: &[String],
    proposition: &ClickProposition,
    active: &mut BTreeSet<String>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::PredicateCall { name, arguments }
            if unfolded_predicates
                .iter()
                .any(|predicate| predicate == name) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_click_predicate_definition(definition, arguments)?;
            let unfolded = unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                &unfolded,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: left.clone(),
            operator: *operator,
            right: right.clone(),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::ForAll { c_type, name, body } => Ok(ClickProposition::ForAll {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::Exists { c_type, name, body } => Ok(ClickProposition::Exists {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments.clone(),
            })
        }
    }
}

fn instantiate_click_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
) -> Result<ClickProposition, String> {
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "predicate `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }

    let substitutions = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect::<BTreeMap<_, _>>();
    substitute_click_proposition(definition.body(), &substitutions)
}

fn substitute_click_proposition(
    proposition: &ClickProposition,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: substitute_contract_expression(left, substitutions)?,
            operator: *operator,
            right: substitute_contract_expression(right, substitutions)?,
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            substitute_click_proposition(body, substitutions)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::ForAll { c_type, name, body } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(item);
            Ok(ClickProposition::RangeAll {
                start: substitute_contract_expression(start, substitutions)?,
                end: substitute_contract_expression(end, substitutions)?,
                item: item.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(item);
            Ok(ClickProposition::RangeAny {
                start: substitute_contract_expression(start, substitutions)?,
                end: substitute_contract_expression(end, substitutions)?,
                item: item.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_contract_expression(argument, substitutions))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    }
}

fn apply_contract_lets_to_requirement(
    requirement: Requirement,
    bindings: &[ContractLetBinding],
) -> Result<Requirement, String> {
    match requirement {
        Requirement::Labeled { label, requirement } => Ok(Requirement::Labeled {
            label,
            requirement: Box::new(apply_contract_lets_to_requirement(*requirement, bindings)?),
        }),
        Requirement::ValidRange { name, bytes } => Ok(Requirement::ValidRange {
            name,
            bytes: apply_contract_lets_to_range_bytes(bytes, bindings)?,
        }),
        Requirement::ValidRangeSegment { segment } => Ok(Requirement::ValidRangeSegment {
            segment: apply_contract_lets_to_segment(segment, bindings)?,
        }),
        Requirement::Disjoint { left, right } => Ok(Requirement::Disjoint {
            left: apply_contract_lets_to_segment(left, bindings)?,
            right: apply_contract_lets_to_segment(right, bindings)?,
        }),
        Requirement::Resource(resource) => Ok(Requirement::Resource(
            apply_contract_lets_to_resource_clause(resource, bindings)?,
        )),
        Requirement::Proposition(proposition) => Ok(Requirement::Proposition(
            apply_contract_lets_to_proposition(proposition, bindings)?,
        )),
    }
}

fn apply_contract_lets_to_ensure_clause(
    clause: EnsureClause,
    bindings: &[ContractLetBinding],
) -> Result<EnsureClause, String> {
    let EnsureClause {
        name,
        ensure,
        proof,
    } = clause;
    let ensure = match ensure {
        Ensure::Proposition(proposition) => {
            Ensure::Proposition(apply_contract_lets_to_proposition(proposition, bindings)?)
        }
        Ensure::Resource(resource) => {
            Ensure::Resource(apply_contract_lets_to_resource_clause(resource, bindings)?)
        }
    };
    Ok(EnsureClause {
        name,
        ensure,
        proof,
    })
}

fn apply_contract_lets_to_resource_clause(
    resource: ResourceClause,
    bindings: &[ContractLetBinding],
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(apply_contract_lets_to_segment(
            segment, bindings,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceClause::Free(segment) => Ok(ResourceClause::Free(apply_contract_lets_to_segment(
            segment, bindings,
        )?)),
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Named {
            name,
            arguments: arguments
                .into_iter()
                .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types,
        }),
    }
}

fn apply_contract_lets_to_effect_clause(
    clause: EffectClause,
    bindings: &[ContractLetBinding],
) -> Result<EffectClause, String> {
    let EffectClause { effect, proof } = clause;
    Ok(EffectClause {
        effect: apply_contract_lets_to_effect(effect, bindings)?,
        proof,
    })
}

fn apply_contract_lets_to_structural_clause(
    clause: StructuralClause,
    bindings: &[ContractLetBinding],
) -> Result<StructuralClause, String> {
    let StructuralClause {
        region,
        label,
        items,
    } = clause;
    let items = items
        .into_iter()
        .map(|item| apply_contract_lets_to_structural_item(item, bindings))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(StructuralClause {
        region,
        label,
        items,
    })
}

fn apply_contract_lets_to_structural_item(
    item: StructuralItem,
    bindings: &[ContractLetBinding],
) -> Result<StructuralItem, String> {
    let StructuralItem { kind, claim, proof } = item;
    let claim = match claim {
        StructuralItemClaim::Proposition(proposition) => StructuralItemClaim::Proposition(
            apply_contract_lets_to_proposition(proposition, bindings)?,
        ),
        StructuralItemClaim::Effect(effect) => {
            StructuralItemClaim::Effect(apply_contract_lets_to_effect(effect, bindings)?)
        }
    };
    Ok(StructuralItem { kind, claim, proof })
}

fn apply_contract_lets_to_effect(
    effect: Effect,
    bindings: &[ContractLetBinding],
) -> Result<Effect, String> {
    match effect {
        Effect::Immutable => Ok(Effect::Immutable),
        Effect::Mutable(segments) => Ok(Effect::Mutable(
            segments
                .into_iter()
                .map(|segment| apply_contract_lets_to_segment(segment, bindings))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

fn apply_contract_lets_to_segment(
    segment: ContractSegment,
    bindings: &[ContractLetBinding],
) -> Result<ContractSegment, String> {
    let substitutions = contract_let_substitutions(bindings);
    let segment = ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, &substitutions)?,
        start: substitute_c_fragment(&segment.start, &substitutions)?,
        end: substitute_c_fragment(&segment.end, &substitutions)?,
    };
    reject_contract_where_let_references(
        &contract_segment_referenced_names(&segment),
        bindings,
        "memory segment expressions",
    )?;
    Ok(segment)
}

fn apply_contract_lets_to_range_bytes(
    bytes: RangeBytes,
    bindings: &[ContractLetBinding],
) -> Result<RangeBytes, String> {
    reject_contract_where_let_references(
        &range_bytes_referenced_names(&bytes),
        bindings,
        "valid_range byte expressions",
    )?;
    let bytes = match bytes {
        RangeBytes::Constant(_) => Ok(bytes),
        RangeBytes::Parameter(name) => {
            let substitutions = contract_let_substitutions(bindings);
            let Some(value) = substitutions.get(&name) else {
                return Ok(RangeBytes::Parameter(name));
            };
            let c_fragment = contract_expression_as_c_fragment(value).ok_or_else(|| {
                format!(
                    "contract `let` `{name}` cannot be used in a valid_range byte expression because it is not a C fragment"
                )
            })?;
            range_bytes_from_c_expression(&c_fragment).ok_or_else(|| {
                format!("contract `let` `{name}` cannot be used in a valid_range byte expression")
            })
        }
        RangeBytes::Add(left, right) => Ok(RangeBytes::Add(
            Box::new(apply_contract_lets_to_range_bytes(*left, bindings)?),
            Box::new(apply_contract_lets_to_range_bytes(*right, bindings)?),
        )),
        RangeBytes::Subtract(left, right) => Ok(RangeBytes::Subtract(
            Box::new(apply_contract_lets_to_range_bytes(*left, bindings)?),
            Box::new(apply_contract_lets_to_range_bytes(*right, bindings)?),
        )),
        RangeBytes::Multiply(left, right) => Ok(RangeBytes::Multiply(
            Box::new(apply_contract_lets_to_range_bytes(*left, bindings)?),
            Box::new(apply_contract_lets_to_range_bytes(*right, bindings)?),
        )),
    }?;
    reject_contract_where_let_references(
        &range_bytes_referenced_names(&bytes),
        bindings,
        "valid_range byte expressions",
    )?;
    Ok(bytes)
}

fn reject_contract_where_let_references(
    referenced_names: &BTreeSet<String>,
    bindings: &[ContractLetBinding],
    context: &str,
) -> Result<(), String> {
    if let Some(binding) = bindings.iter().find(|binding| {
        binding.where_condition().is_some() && referenced_names.contains(&binding.name)
    }) {
        return Err(format!(
            "`let ... where` `{}` cannot be used in {context} yet",
            binding.name
        ));
    }
    Ok(())
}

fn range_bytes_referenced_names(bytes: &RangeBytes) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_range_bytes_referenced_names(bytes, &mut names);
    names
}

fn collect_range_bytes_referenced_names(bytes: &RangeBytes, names: &mut BTreeSet<String>) {
    match bytes {
        RangeBytes::Constant(_) => {}
        RangeBytes::Parameter(name) => {
            names.insert(name.clone());
        }
        RangeBytes::Add(left, right)
        | RangeBytes::Subtract(left, right)
        | RangeBytes::Multiply(left, right) => {
            collect_range_bytes_referenced_names(left, names);
            collect_range_bytes_referenced_names(right, names);
        }
    }
}

fn range_bytes_from_c_expression(expression: &CExpression) -> Option<RangeBytes> {
    match expression {
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
            Some(RangeBytes::Constant(*value))
        }
        CExpression::Variable(name) => Some(RangeBytes::Parameter(name.clone())),
        CExpression::Add(left, right) => Some(RangeBytes::Add(
            Box::new(range_bytes_from_c_expression(left)?),
            Box::new(range_bytes_from_c_expression(right)?),
        )),
        CExpression::Subtract(left, right) => Some(RangeBytes::Subtract(
            Box::new(range_bytes_from_c_expression(left)?),
            Box::new(range_bytes_from_c_expression(right)?),
        )),
        CExpression::Multiply(left, right) => Some(RangeBytes::Multiply(
            Box::new(range_bytes_from_c_expression(left)?),
            Box::new(range_bytes_from_c_expression(right)?),
        )),
        _ => None,
    }
}

fn apply_contract_lets_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    let proposition = apply_contract_let_expressions_to_proposition(proposition, bindings)?;
    wrap_contract_where_lets_proposition(proposition, bindings)
}

fn apply_contract_let_expressions_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: apply_contract_lets_to_expression(left, bindings)?,
            operator,
            right: apply_contract_lets_to_expression(right, bindings)?,
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            apply_contract_let_expressions_to_proposition(*body, bindings)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::ForAll { c_type, name, body } => {
            let scoped = contract_lets_without_name(bindings, &name);
            Ok(ClickProposition::ForAll {
                c_type,
                name,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            let scoped = contract_lets_without_name(bindings, &name);
            Ok(ClickProposition::Exists {
                c_type,
                name,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            Ok(ClickProposition::RangeAll {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            Ok(ClickProposition::RangeAny {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    }
}

fn wrap_contract_where_lets_proposition(
    mut proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    for (index, binding) in bindings.iter().enumerate().rev() {
        let Some(condition) = binding.where_condition() else {
            continue;
        };
        let condition =
            apply_contract_let_expressions_to_proposition(condition.clone(), &bindings[..index])?;
        let Some(c_type) = binding.c_type else {
            return Err(format!(
                "`let ... where` `{}` requires an explicit type annotation",
                binding.name
            ));
        };
        proposition = ClickProposition::Exists {
            c_type,
            name: binding.name.clone(),
            body: Box::new(ClickProposition::And(
                Box::new(condition),
                Box::new(proposition),
            )),
        };
    }
    Ok(proposition)
}

fn apply_contract_lets_to_expression(
    expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> Result<ContractExpression, String> {
    let referenced_names = contract_expression_referenced_names(&expression);
    let referenced_bindings = bindings
        .iter()
        .filter(|binding| binding.value().is_some() && referenced_names.contains(&binding.name))
        .cloned()
        .collect::<Vec<_>>();
    let substitutions = contract_let_substitutions(bindings);
    let expression = substitute_contract_expression(&expression, &substitutions)?;
    Ok(wrap_contract_lets_expression(
        expression,
        &referenced_bindings,
    ))
}

fn wrap_contract_lets_expression(
    mut expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> ContractExpression {
    for binding in bindings.iter().rev() {
        let Some(value) = binding.value() else {
            continue;
        };
        expression = ContractExpression::Let {
            name: binding.name.clone(),
            c_type: binding.c_type,
            value: Box::new(value.clone()),
            body: Box::new(expression),
        };
    }
    expression
}

fn contract_lets_without_name(
    bindings: &[ContractLetBinding],
    name: &str,
) -> Vec<ContractLetBinding> {
    bindings
        .iter()
        .filter(|binding| binding.name != name)
        .cloned()
        .collect()
}

fn contract_expression_referenced_names(expression: &ContractExpression) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_contract_expression_referenced_names(expression, &mut names);
    names
}

fn collect_contract_expression_referenced_names(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::CFragment(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        ContractExpression::Old(expression) | ContractExpression::BitwiseNot(expression) => {
            collect_contract_expression_referenced_names(expression, names);
        }
        ContractExpression::At { expression, .. } => {
            collect_contract_expression_referenced_names(expression, names);
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
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_proposition_referenced_names(condition, names);
            collect_contract_expression_referenced_names(then_branch, names);
            collect_contract_expression_referenced_names(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            collect_contract_expression_referenced_names(initial, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_names(body, &mut body_names);
            body_names.remove(accumulator);
            body_names.remove(item);
            names.extend(body_names);
        }
        ContractExpression::Let {
            name, value, body, ..
        } => {
            collect_contract_expression_referenced_names(value, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_names(body, &mut body_names);
            body_names.remove(name);
            names.extend(body_names);
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

fn collect_click_proposition_referenced_names(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_proposition_referenced_names(left, names);
            collect_click_proposition_referenced_names(right, names);
        }
        ClickProposition::Not(body) => collect_click_proposition_referenced_names(body, names),
        ClickProposition::ForAll { name, body, .. }
        | ClickProposition::Exists { name, body, .. } => {
            let mut body_names = BTreeSet::new();
            collect_click_proposition_referenced_names(body, &mut body_names);
            body_names.remove(name);
            names.extend(body_names);
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            let mut body_names = BTreeSet::new();
            collect_click_proposition_referenced_names(body, &mut body_names);
            body_names.remove(item);
            names.extend(body_names);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

fn contract_let_substitutions(
    bindings: &[ContractLetBinding],
) -> BTreeMap<String, ContractExpression> {
    bindings
        .iter()
        .filter_map(|binding| {
            binding
                .value()
                .map(|value| (binding.name.clone(), value.clone()))
        })
        .collect()
}

fn substitute_contract_expression(
    expression: &ContractExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractExpression, String> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name)) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| expression.clone())),
        ContractExpression::CFragment(expression) => {
            substitute_c_fragment_as_contract(expression, substitutions)
        }
        ContractExpression::Old(expression) => Ok(ContractExpression::Old(Box::new(
            substitute_contract_expression(expression, substitutions)?,
        ))),
        ContractExpression::At {
            selector,
            expression,
        } => Ok(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(substitute_contract_expression(expression, substitutions)?),
        }),
        ContractExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_contract_expression(expression, substitutions)?,
        ))),
        ContractExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_contract_expression(base, substitutions)?),
            Box::new(substitute_contract_expression(index, substitutions)?),
        )),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => Ok(ContractExpression::If {
            condition: Box::new(substitute_click_proposition(condition, substitutions)?),
            then_branch: Box::new(substitute_contract_expression(then_branch, substitutions)?),
            else_branch: Box::new(substitute_contract_expression(else_branch, substitutions)?),
        }),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(accumulator);
            scoped.remove(item);
            Ok(ContractExpression::RangeFold {
                start: Box::new(substitute_contract_expression(start, substitutions)?),
                end: Box::new(substitute_contract_expression(end, substitutions)?),
                initial: Box::new(substitute_contract_expression(initial, substitutions)?),
                accumulator: accumulator.clone(),
                item: item.clone(),
                body: Box::new(substitute_contract_expression(body, &scoped)?),
            })
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ContractExpression::Let {
                name: name.clone(),
                c_type: *c_type,
                value: Box::new(substitute_contract_expression(value, substitutions)?),
                body: Box::new(substitute_contract_expression(body, &scoped)?),
            })
        }
        ContractExpression::Call { name, arguments } => Ok(ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

fn substitute_c_fragment_as_contract(
    expression: &CExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractExpression, String> {
    match expression {
        CExpression::Value(_) => Ok(ContractExpression::CFragment(expression.clone())),
        CExpression::Variable(name) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ContractExpression::CFragment(expression.clone()))),
        CExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_c_fragment_as_contract(expression, substitutions)?,
        ))),
        CExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_c_fragment_as_contract(base, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(index, substitutions)?),
        )),
        _ => Ok(ContractExpression::CFragment(substitute_c_fragment(
            expression,
            substitutions,
        )?)),
    }
}

fn substitute_c_fragment(
    expression: &CExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<CExpression, String> {
    match expression {
        CExpression::Value(_) => Ok(expression.clone()),
        CExpression::Variable(name) => {
            let Some(substitution) = substitutions.get(name) else {
                return Ok(expression.clone());
            };
            contract_expression_as_c_fragment(substitution).ok_or_else(|| {
                format!(
                    "cannot substitute non-C-fragment expression for `{name}` inside C fragment `{expression:?}`"
                )
            })
        }
        CExpression::AddressOf(body) => Ok(CExpression::AddressOf(Box::new(
            substitute_c_fragment(body, substitutions)?,
        ))),
        CExpression::LessThan(left, right) => Ok(CExpression::LessThan(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::LessEqual(left, right) => Ok(CExpression::LessEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::GreaterThan(left, right) => Ok(CExpression::GreaterThan(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::GreaterEqual(left, right) => Ok(CExpression::GreaterEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Equal(left, right) => Ok(CExpression::Equal(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::NotEqual(left, right) => Ok(CExpression::NotEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Not(body) => Ok(CExpression::Not(Box::new(substitute_c_fragment(
            body,
            substitutions,
        )?))),
        CExpression::And(left, right) => Ok(CExpression::And(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Or(left, right) => Ok(CExpression::Or(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            substitute_c_fragment(expression, substitutions)?,
        ))),
        CExpression::Load(body) => Ok(CExpression::Load(Box::new(substitute_c_fragment(
            body,
            substitutions,
        )?))),
        CExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(substitute_c_fragment(base, substitutions)?),
            Box::new(substitute_c_fragment(index, substitutions)?),
        )),
    }
}

fn contract_expression_as_c_fragment(expression: &ContractExpression) -> Option<CExpression> {
    match expression {
        ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(CExpression::BitwiseNot(Box::new(
            contract_expression_as_c_fragment(expression)?,
        ))),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_as_c_fragment(base)?),
            Box::new(contract_expression_as_c_fragment(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

fn structural_item_kind_label(kind: StructuralItemKind) -> &'static str {
    match kind {
        StructuralItemKind::Assert => "assert",
        StructuralItemKind::Invariant => "invariant",
        StructuralItemKind::Effect => "effect",
        StructuralItemKind::StepEffect => "step effect",
    }
}

fn prepend_labeled_asserts(statement: CStatement, checks: &[LabeledCheck]) -> CStatement {
    checks.iter().rev().fold(statement, |statement, check| {
        c_seq(
            c_labeled_assert(check.condition.clone(), check.label.clone()),
            statement,
        )
    })
}

fn click_proposition_to_c_expression(proposition: &ClickProposition) -> Option<CExpression> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = contract_expression_to_c_fragment(left)?;
            let right = contract_expression_to_c_fragment(right)?;
            Some(match operator {
                ComparisonOperator::Equal => CExpression::Equal(Box::new(left), Box::new(right)),
                ComparisonOperator::NotEqual => {
                    CExpression::NotEqual(Box::new(left), Box::new(right))
                }
                ComparisonOperator::LessThan => {
                    CExpression::LessThan(Box::new(left), Box::new(right))
                }
                ComparisonOperator::LessEqual => {
                    CExpression::LessEqual(Box::new(left), Box::new(right))
                }
                ComparisonOperator::GreaterThan => {
                    CExpression::GreaterThan(Box::new(left), Box::new(right))
                }
                ComparisonOperator::GreaterEqual => {
                    CExpression::GreaterEqual(Box::new(left), Box::new(right))
                }
            })
        }
        ClickProposition::And(left, right) => Some(CExpression::And(
            Box::new(click_proposition_to_c_expression(left)?),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Or(left, right) => Some(CExpression::Or(
            Box::new(click_proposition_to_c_expression(left)?),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Not(body) => Some(CExpression::Not(Box::new(
            click_proposition_to_c_expression(body)?,
        ))),
        ClickProposition::Implies(left, right) => Some(CExpression::Or(
            Box::new(CExpression::Not(Box::new(
                click_proposition_to_c_expression(left)?,
            ))),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::ForAll { .. }
        | ClickProposition::Exists { .. }
        | ClickProposition::RangeAll { .. }
        | ClickProposition::RangeAny { .. }
        | ClickProposition::PredicateCall { .. } => None,
    }
}

fn c_comparison_operator(operator: ComparisonOperator) -> CComparisonOperator {
    match operator {
        ComparisonOperator::Equal => CComparisonOperator::Equal,
        ComparisonOperator::NotEqual => CComparisonOperator::NotEqual,
        ComparisonOperator::LessThan => CComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => CComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => CComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => CComparisonOperator::GreaterEqual,
    }
}

fn contract_expression_to_c_fragment(expression: &ContractExpression) -> Option<CExpression> {
    match expression {
        ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(CExpression::BitwiseNot(Box::new(
            contract_expression_to_c_fragment(expression)?,
        ))),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_to_c_fragment(base)?),
            Box::new(contract_expression_to_c_fragment(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

fn count_loops(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => count_loops(first) + count_loops(second),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => count_loops(then_branch) + count_loops(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_loops(body),
        _ => 0,
    }
}

fn count_statements(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => {
            count_statements(first) + count_statements(second)
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => 1 + count_statements(then_branch) + count_statements(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_statements(body),
        _ => 1,
    }
}

fn c0_loop_modified_locals(statement: &syntax::C0Statement) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c0_loop_modified_locals(statement, &mut names);
    names
}

fn collect_c0_loop_modified_locals(statement: &syntax::C0Statement, names: &mut BTreeSet<String>) {
    match statement {
        syntax::C0Statement::Declare { .. }
        | syntax::C0Statement::Return(_)
        | syntax::C0Statement::Store { .. }
        | syntax::C0Statement::Free { .. } => {}
        syntax::C0Statement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        syntax::C0Statement::CallAssign { target, .. } => {
            names.insert(target.clone());
        }
        syntax::C0Statement::Seq(first, second) => {
            collect_c0_loop_modified_locals(first, names);
            collect_c0_loop_modified_locals(second, names);
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_c0_loop_modified_locals(then_branch, names);
            collect_c0_loop_modified_locals(else_branch, names);
        }
        syntax::C0Statement::While { body, .. } => {
            collect_c0_loop_modified_locals(body, names);
        }
    }
}

fn contract_segment_referenced_names(segment: &ContractSegment) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c_expression_referenced_names(&segment.base, &mut names);
    collect_c_expression_referenced_names(&segment.start, &mut names);
    collect_c_expression_referenced_names(&segment.end, &mut names);
    names
}

fn collect_c_expression_referenced_names(expression: &CExpression, names: &mut BTreeSet<String>) {
    match expression {
        CExpression::Value(_) => {}
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::AddressOf(expression)
        | CExpression::Not(expression)
        | CExpression::Load(expression) => {
            collect_c_expression_referenced_names(expression, names);
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
            collect_c_expression_referenced_names(left, names);
            collect_c_expression_referenced_names(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
    }
}

fn initial_call(
    function_name: &str,
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(CState, Vec<CExpression>, Vec<Proposition>), ClickError> {
    let mut arguments = Vec::new();

    for (index, parameter) in parameters.iter().enumerate() {
        match parameter.c_type() {
            C0Type::Int32Pointer => {
                arguments.push(c_pointer_value(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }));
            }
            C0Type::UInt8Pointer => {
                arguments.push(c_pointer_value(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                }));
            }
            C0Type::Int32 => {
                arguments.push(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt8 => {
                arguments.push(CExpression::Value(CValue::UInt8(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Int32Array(_) | C0Type::UInt8Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
        }
    }

    let mut valid_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, bytes)) =
            concrete_valid_range_block(requirement, parameters, &arguments)?
        {
            valid_ranges.insert(name, bytes);
        }
        if let Requirement::Resource(resource) = requirement.inner() {
            if let Some((name, bytes)) =
                concrete_write_resource_block(resource, parameters, &arguments)?
            {
                valid_ranges.insert(name, bytes);
            }
        }
    }

    for name in requires.iter().filter_map(requirement_valid_range_name) {
        if !parameters.iter().any(|parameter| parameter.name() == name) {
            return Err(ClickError::new(format!(
                "`valid_range` names `{name}`, but `{}` has no such parameter",
                function_name
            )));
        }
    }

    let mut memory = CMemory::new();
    memory = memory_with_symbolic_valid_range_cells(memory, &valid_ranges);
    let resources = resource_context_from_requirements(requires, parameters, &arguments, &memory)?;
    let requirement_propositions = requirement_propositions(
        requires,
        parameters,
        &arguments,
        &memory,
        predicate_environment,
        click_function_environment,
    )?;
    Ok((
        CState::new()
            .with_memory(memory)
            .with_resource_context(resources),
        arguments,
        requirement_propositions,
    ))
}

fn memory_with_symbolic_valid_range_cells(
    mut memory: CMemory,
    valid_ranges: &BTreeMap<String, (Pointer, u32)>,
) -> CMemory {
    let base_memory = memory.clone();
    for (base, bytes) in valid_ranges.values() {
        let mut offset: u32 = 0;
        while offset.checked_add(4).is_some_and(|end| end <= *bytes) {
            let pointer = offset_pointer_by_int32_elements(
                base.clone(),
                Bitvector32Term::Constant(offset / 4),
            );
            let value = CValue::Int32(Bitvector32Term::MemoryLoad(
                Box::new(base_memory.clone()),
                Box::new(pointer.clone()),
            ));
            memory = memory.store(pointer, value);
            offset += 4;
        }
    }
    memory
}

fn requirement_propositions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, ClickError> {
    let mut propositions = Vec::new();
    for requirement in requires {
        let proposition = match requirement.inner() {
            Requirement::ValidRange { .. } | Requirement::ValidRangeSegment { .. } => {
                valid_range_requirement_prop(requirement, parameters, arguments, memory)?
            }
            Requirement::Disjoint { left, right } => {
                disjoint_requirement_prop(parameters, arguments, memory, left, right)?
            }
            Requirement::Proposition(proposition) => requirement_proposition_prop(
                parameters,
                arguments,
                memory,
                proposition,
                predicate_environment,
                click_function_environment,
            )?,
            Requirement::Resource(_) => continue,
            Requirement::Labeled { .. } => unreachable!("requirement.inner() removes labels"),
        };
        propositions.push(proposition);
    }
    Ok(propositions)
}

fn resource_context_from_requirements(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<ResourceContext, ClickError> {
    let mut context = ResourceContext::new();
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement.inner() {
            context = context.with_resource(lower_resource_clause(
                resource, parameters, arguments, memory,
            )?);
        }
    }
    Ok(context)
}

fn lower_resource_clause(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<CResource, ClickError> {
    match resource {
        ResourceClause::Read(segment) => {
            let range = lower_resource_segment("read", segment, parameters, arguments, memory)?;
            Ok(CResource::Read(range))
        }
        ResourceClause::Write(segment) => {
            let range = lower_resource_segment("write", segment, parameters, arguments, memory)?;
            Ok(CResource::Write(range))
        }
        ResourceClause::Free(segment) => {
            let range = lower_resource_segment("free", segment, parameters, arguments, memory)?;
            Ok(CResource::Free(range))
        }
        ResourceClause::Named {
            name,
            arguments: resource_arguments,
            parameter_types,
        } => {
            let parameter_values = parameter_values(parameters, arguments)
                .map_err(|error| ClickError::new(error.message))?;
            let state = CState::new().with_memory(memory.clone());
            let assumptions = Assumptions::new();
            let mut values = Vec::new();
            if resource_arguments.len() != parameter_types.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata"
                )));
            }
            for (index, (argument, parameter_type)) in
                resource_arguments.iter().zip(parameter_types).enumerate()
            {
                let argument = resource_argument_to_c_expression(argument)?;
                let value = evaluate_c_contract_expression(
                    &parameter_values,
                    &state,
                    None,
                    &assumptions,
                    &argument,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "could not lower resource `{name}` argument {index}: {message}"
                    ))
                })?;
                if !c_value_matches_click_type(&value, *parameter_type) {
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                        parameter_type
                    )));
                }
                values.push(value);
            }
            Ok(CResource::Named {
                name: name.clone(),
                arguments: values,
            })
        }
    }
}

fn resource_argument_to_c_expression(
    argument: &ContractExpression,
) -> Result<CExpression, ClickError> {
    match argument {
        ContractExpression::CFragment(expression) => Ok(expression.clone()),
        ContractExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            resource_argument_to_c_expression(expression)?,
        ))),
        ContractExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(resource_argument_to_c_expression(base)?),
            Box::new(resource_argument_to_c_expression(index)?),
        )),
        ContractExpression::Old(_)
        | ContractExpression::At { .. }
        | ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. }
        | ContractExpression::Call { .. } => Err(ClickError::new(
            "named resource arguments currently support current-state C expressions only",
        )),
    }
}

fn lower_resource_segment(
    resource_name: &str,
    segment: &ContractSegment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<CMemoryRange, ClickError> {
    let state = CState::new().with_memory(memory.clone());
    let segment = evaluate_requirement_segment(parameters, arguments, &state, segment).map_err(
        |message| {
            ClickError::new(format!(
                "could not lower `{resource_name}` resource: {message}"
            ))
        },
    )?;
    if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
    {
        if end < start {
            return Err(ClickError::new(format!(
                "`{resource_name}` segment has an end before its start: {start}..{end}"
            )));
        }
    }
    Ok(CMemoryRange::new(segment.base, segment.start, segment.end))
}

fn valid_range_requirement_prop(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Proposition, ClickError> {
    let (base, bytes) = valid_range_base_and_bytes(requirement, parameters, arguments)?;
    Ok(Proposition::CMemoryValidRange {
        memory: memory.clone(),
        base,
        bytes,
    })
}

fn requirement_valid_range_name(requirement: &Requirement) -> Option<&str> {
    match requirement.inner() {
        Requirement::ValidRange { name, .. } => Some(name),
        Requirement::Labeled { .. }
        | Requirement::ValidRangeSegment { .. }
        | Requirement::Disjoint { .. }
        | Requirement::Resource(_)
        | Requirement::Proposition(_) => None,
    }
}

fn concrete_valid_range_block(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, (Pointer, u32))>, ClickError> {
    match requirement.inner() {
        Requirement::ValidRange { name, bytes } => {
            let Some(bytes) = range_bytes_constant(bytes) else {
                return Ok(None);
            };
            let Some((_, argument)) = parameters
                .iter()
                .zip(arguments)
                .find(|(parameter, _)| parameter.name() == name)
            else {
                return Ok(None);
            };
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return Ok(None);
            };
            Ok(Some((name.clone(), (base.clone(), bytes))))
        }
        Requirement::ValidRangeSegment { segment } => {
            let state = CState::new();
            let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment)
            else {
                return Ok(None);
            };
            if segment.base.offset != PointerOffsetTerm::Constant(0)
                || segment.start != Bitvector32Term::Constant(0)
            {
                return Ok(None);
            }
            let Bitvector32Term::Constant(end) = segment.end else {
                return Ok(None);
            };
            let element_width = contract_segment_element_width(parameters, &segment.source);
            let bytes = end
                .checked_mul(element_width)
                .ok_or_else(|| ClickError::new("`valid_range` segment overflows byte count"))?;
            Ok(Some((
                format!("{:?}", segment.source),
                (segment.base, bytes),
            )))
        }
        Requirement::Labeled { .. }
        | Requirement::Resource(_)
        | Requirement::Disjoint { .. }
        | Requirement::Proposition(_) => Ok(None),
    }
}

fn concrete_write_resource_block(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, (Pointer, u32))>, ClickError> {
    let ResourceClause::Write(segment) = resource else {
        return Ok(None);
    };
    let state = CState::new();
    let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment) else {
        return Ok(None);
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
    else {
        return Ok(None);
    };
    if end < start {
        return Err(ClickError::new(format!(
            "`write` segment has an end before its start: {start}..{end}"
        )));
    }
    let element_width = contract_segment_element_width(parameters, &segment.source);
    let element_count = end - start;
    let bytes = element_count
        .checked_mul(element_width)
        .ok_or_else(|| ClickError::new("`write` segment overflows byte count"))?;
    Ok(Some((
        format!("{:?}", segment.source),
        (
            offset_pointer_by_elements(segment.base, segment.start, element_width),
            bytes,
        ),
    )))
}

fn valid_range_base_and_bytes(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<(Pointer, Bitvector32Term), ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;

    match requirement.inner() {
        Requirement::ValidRange { name, bytes } => {
            let Some((_, argument)) = parameters
                .iter()
                .zip(arguments)
                .find(|(parameter, _)| parameter.name() == name)
            else {
                return Err(ClickError::new(format!(
                    "`valid_range` names `{name}`, but no such parameter exists"
                )));
            };
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return Err(ClickError::new(format!(
                    "`valid_range` names `{name}`, but it is not a pointer parameter"
                )));
            };
            Ok((base.clone(), lower_range_bytes(bytes, &parameter_values)?))
        }
        Requirement::ValidRangeSegment { segment } => {
            let state = CState::new();
            let segment = evaluate_requirement_segment(parameters, arguments, &state, segment)
                .map_err(|message| {
                    ClickError::new(format!("could not lower `valid_range` segment: {message}"))
                })?;
            if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
                (&segment.start, &segment.end)
            {
                if end < start {
                    return Err(ClickError::new(format!(
                        "`valid_range` segment has an end before its start: {start}..{end}"
                    )));
                }
            }
            let element_count = bitvector32_subtract(segment.end.clone(), segment.start.clone());
            let element_width = contract_segment_element_width(parameters, &segment.source);
            let bytes =
                bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
            Ok((
                offset_pointer_by_elements(segment.base, segment.start, element_width),
                bytes,
            ))
        }
        Requirement::Labeled { .. }
        | Requirement::Proposition(_)
        | Requirement::Resource(_)
        | Requirement::Disjoint { .. } => Err(ClickError::new("expected valid_range requirement")),
    }
}

fn disjoint_requirement_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    left: &ContractSegment,
    right: &ContractSegment,
) -> Result<Proposition, ClickError> {
    let state = CState::new().with_memory(memory.clone());
    let left =
        evaluate_requirement_segment(parameters, arguments, &state, left).map_err(|message| {
            ClickError::new(format!("could not lower `disjoint` left range: {message}"))
        })?;
    let right =
        evaluate_requirement_segment(parameters, arguments, &state, right).map_err(|message| {
            ClickError::new(format!("could not lower `disjoint` right range: {message}"))
        })?;
    Ok(Proposition::CMemoryDisjoint {
        left_base: left.base,
        left_start: left.start,
        left_end: left.end,
        right_base: right.base,
        right_start: right.start,
        right_end: right.end,
    })
}

fn contract_segment_element_width(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> u32 {
    contract_expression_element_width(parameters, &segment.base).unwrap_or(4)
}

fn contract_expression_element_width(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> Option<u32> {
    match expression {
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(|parameter| match parameter.c_type() {
                C0Type::Int32Pointer => Some(4),
                C0Type::UInt8Pointer => Some(1),
                _ => None,
            }),
        CExpression::Add(left, right) => contract_expression_element_width(parameters, left)
            .or_else(|| contract_expression_element_width(parameters, right)),
        CExpression::Subtract(left, _) => contract_expression_element_width(parameters, left),
        _ => None,
    }
}

fn range_bytes_constant(bytes: &RangeBytes) -> Option<u32> {
    match bytes {
        RangeBytes::Constant(value) => Some(*value),
        RangeBytes::Parameter(_) => None,
        RangeBytes::Add(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_add(range_bytes_constant(right)?))
        }
        RangeBytes::Subtract(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_sub(range_bytes_constant(right)?))
        }
        RangeBytes::Multiply(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_mul(range_bytes_constant(right)?))
        }
    }
}

fn lower_range_bytes(
    bytes: &RangeBytes,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<Bitvector32Term, ClickError> {
    match bytes {
        RangeBytes::Constant(value) => Ok(Bitvector32Term::Constant(*value)),
        RangeBytes::Parameter(name) => match parameter_values.get(name) {
            Some(CValue::Int32(bits)) => Ok(bits.clone()),
            Some(_) => Err(ClickError::new(format!(
                "`valid_range` byte expression references pointer parameter `{name}`"
            ))),
            None => Err(ClickError::new(format!(
                "`valid_range` byte expression references unknown parameter `{name}`"
            ))),
        },
        RangeBytes::Add(left, right) => Ok(bitvector32_add(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
        RangeBytes::Subtract(left, right) => Ok(bitvector32_subtract(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
        RangeBytes::Multiply(left, right) => Ok(bitvector32_multiply(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
    }
}

fn requirement_proposition_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, memory);
    let mut lowerer = KernelPropositionLowerer::new(
        parameter_values,
        array_refs,
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    lowerer.lower_requirement_proposition(proposition)
}

fn parameter_values(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<BTreeMap<String, CValue>, ClickError> {
    parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            let CExpression::Value(value) = argument else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    parameter.name()
                )));
            };
            Ok((parameter.name().to_string(), value.clone()))
        })
        .collect()
}

fn array_refs_for_parameters(
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.c_type())?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

struct KernelPropositionLowerer {
    values: BTreeMap<String, CValue>,
    array_refs: ClickArrayRefs,
    memory: CMemory,
    predicate_environment: PredicateEnvironment,
    click_function_environment: ClickFunctionEnvironment,
    active_functions: BTreeSet<String>,
    next_variable: u64,
}

impl KernelPropositionLowerer {
    fn new(
        values: BTreeMap<String, CValue>,
        array_refs: ClickArrayRefs,
        memory: CMemory,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
    ) -> Self {
        Self {
            values,
            array_refs,
            memory,
            predicate_environment: predicate_environment.clone(),
            click_function_environment: click_function_environment.clone(),
            active_functions: BTreeSet::new(),
            next_variable: 2_000_000,
        }
    }

    fn lower_requirement_proposition(
        &mut self,
        proposition: &ClickProposition,
    ) -> Result<Proposition, ClickError> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                comparison_proposition(left, *operator, right)
            }
            ClickProposition::And(left, right) => Ok(Proposition::And(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Or(left, right) => Ok(Proposition::Or(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
                self.lower_requirement_proposition(body)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(Proposition::Implies(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err(ClickError::new("only `forall (int32 ...)` is supported"));
                }
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let previous = self.values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.lower_requirement_proposition(body)?;
                match previous {
                    Some(value) => {
                        self.values.insert(name.clone(), value);
                    }
                    None => {
                        self.values.remove(name);
                    }
                }
                Ok(Proposition::ForAll {
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                })
            }
            ClickProposition::Exists { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err(ClickError::new("only `exists (int32 ...)` is supported"));
                }
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let previous = self.values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.lower_requirement_proposition(body)?;
                match previous {
                    Some(value) => {
                        self.values.insert(name.clone(), value);
                    }
                    None => {
                        self.values.remove(name);
                    }
                }
                Ok(Proposition::Exists {
                    name: name.clone(),
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                })
            }
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => {
                let start = int32_term_value(
                    self.lower_requirement_value(start)?,
                    "range `all` start bound",
                )
                .map_err(ClickError::new)?;
                let end =
                    int32_term_value(self.lower_requirement_value(end)?, "range `all` end bound")
                        .map_err(ClickError::new)?;
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let item_value = CValue::Int32(Bitvector32Term::Variable(variable));
                let outer_values = self.values.clone();
                self.values.insert(item.clone(), item_value.clone());
                let body = match self.lower_requirement_proposition(body) {
                    Ok(body) => body,
                    Err(error) => {
                        self.values = outer_values;
                        return Err(error);
                    }
                };
                self.values = outer_values;
                let CValue::Int32(item_bits) = item_value else {
                    unreachable!("range `all` item value is always int32")
                };
                Ok(bounded_forall_int32(variable, start, item_bits, end, body))
            }
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => {
                let start = int32_term_value(
                    self.lower_requirement_value(start)?,
                    "range `any` start bound",
                )
                .map_err(ClickError::new)?;
                let end =
                    int32_term_value(self.lower_requirement_value(end)?, "range `any` end bound")
                        .map_err(ClickError::new)?;
                let outer_values = self.values.clone();
                match (
                    concrete_bound_from_term(&start, "any", "start"),
                    concrete_bound_from_term(&end, "any", "end"),
                ) {
                    (Ok(start), Ok(end)) => {
                        let mut proposition = false_proposition();
                        for index in concrete_fold_range(start, end).map_err(ClickError::new)? {
                            self.values = outer_values.clone();
                            self.values.insert(
                                item.clone(),
                                CValue::Int32(Bitvector32Term::Constant(index as u32)),
                            );
                            let body = match self.lower_requirement_proposition(body) {
                                Ok(body) => body,
                                Err(error) => {
                                    self.values = outer_values;
                                    return Err(error);
                                }
                            };
                            proposition = disjunction(proposition, body);
                        }
                        self.values = outer_values;
                        Ok(proposition)
                    }
                    _ => {
                        let variable = Variable(self.next_variable);
                        self.next_variable += 1;
                        let item_value = CValue::Int32(Bitvector32Term::Variable(variable));
                        self.values.insert(item.clone(), item_value.clone());
                        let body = match self.lower_requirement_proposition(body) {
                            Ok(body) => body,
                            Err(error) => {
                                self.values = outer_values;
                                return Err(error);
                            }
                        };
                        self.values = outer_values;
                        let CValue::Int32(item_bits) = item_value else {
                            unreachable!("range `any` item value is always int32")
                        };
                        Ok(bounded_exists_int32(
                            item.clone(),
                            variable,
                            start,
                            item_bits,
                            end,
                            body,
                        ))
                    }
                }
            }
            ClickProposition::PredicateCall { name, arguments } => {
                let definition = self
                    .predicate_environment
                    .get(name)
                    .ok_or_else(|| ClickError::new(format!("unknown predicate `{name}`")))?;
                let state = CState::new().with_memory(self.memory.clone());
                let lowered_arguments = lower_predicate_call_arguments_with_environment(
                    definition,
                    arguments,
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &Assumptions::new(),
                    &self.predicate_environment,
                    &self.click_function_environment,
                    &mut self.active_functions,
                )
                .map_err(ClickError::new)?;
                Ok(Proposition::Predicate {
                    name: name.clone(),
                    arguments: lowered_arguments,
                })
            }
        }
    }

    fn lower_requirement_value(
        &mut self,
        expression: &ContractExpression,
    ) -> Result<CValue, ClickError> {
        match expression {
            ContractExpression::CFragment(expression) => {
                self.lower_requirement_c_expression(expression)
            }
            ContractExpression::Old(_) => Err(ClickError::new(
                "`old(...)` is not available in `requires` clauses",
            )),
            ContractExpression::At { .. } => Err(ClickError::new(
                "`at(...)` is not available in `requires` clauses",
            )),
            ContractExpression::Add(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_add(left, right)
            }
            ContractExpression::Subtract(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_subtract(left, right)
            }
            ContractExpression::Multiply(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_multiply(left, right)
            }
            ContractExpression::Divide(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_divide(left, right)
            }
            ContractExpression::Remainder(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_remainder(left, right)
            }
            ContractExpression::ShiftLeft(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_shift_left(left, right)
            }
            ContractExpression::ShiftRight(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_shift_right(left, right)
            }
            ContractExpression::BitwiseAnd(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_bitwise_binary(left, right, "&", bitvector32_and)
            }
            ContractExpression::BitwiseOr(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_bitwise_binary(left, right, "|", bitvector32_or)
            }
            ContractExpression::BitwiseXor(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_bitwise_binary(left, right, "^", bitvector32_xor)
            }
            ContractExpression::BitwiseNot(expression) => {
                let value = self.lower_requirement_value(expression)?;
                lower_contract_bitwise_not(value)
            }
            ContractExpression::Index(_, _) => Err(ClickError::new(
                "memory reads are not supported in `requires` propositions yet",
            )),
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.lower_requirement_proposition(condition)?;
                let assumptions = Assumptions::new();
                if assumptions.proves(&condition) {
                    return self.lower_requirement_value(then_branch);
                }
                if assumptions_prove_proposition_false(&assumptions, &condition) {
                    return self.lower_requirement_value(else_branch);
                }

                let then_value = self.lower_requirement_value(then_branch)?;
                let else_value = self.lower_requirement_value(else_branch)?;
                conditional_contract_value(&condition, then_value, else_value)
                    .map_err(ClickError::new)
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let start = int32_term_value(self.lower_requirement_value(start)?, "fold start")
                    .map_err(ClickError::new)?;
                let end = int32_term_value(self.lower_requirement_value(end)?, "fold end")
                    .map_err(ClickError::new)?;
                let mut value = self.lower_requirement_value(initial)?;
                let outer_values = self.values.clone();
                match (
                    concrete_bound_from_term(&start, "fold", "start"),
                    concrete_bound_from_term(&end, "fold", "end"),
                ) {
                    (Ok(start), Ok(end)) => {
                        for index in concrete_fold_range(start, end).map_err(ClickError::new)? {
                            self.values = outer_values.clone();
                            self.values.insert(accumulator.clone(), value);
                            self.values.insert(
                                item.clone(),
                                CValue::Int32(Bitvector32Term::Constant(index as u32)),
                            );
                            match self.lower_requirement_value(body) {
                                Ok(next) => value = next,
                                Err(error) => {
                                    self.values = outer_values;
                                    return Err(error);
                                }
                            }
                        }
                        self.values = outer_values;
                        Ok(value)
                    }
                    _ => {
                        self.values = outer_values.clone();
                        self.values.insert(accumulator.clone(), value.clone());
                        self.values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                        );
                        self.values.insert(
                            accumulator.clone(),
                            CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                                accumulator,
                                0,
                            ))),
                        );
                        let body_value = match self.lower_requirement_value(body) {
                            Ok(body_value) => body_value,
                            Err(error) => {
                                self.values = outer_values;
                                return Err(error);
                            }
                        };
                        self.values = outer_values;
                        symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                            .map_err(ClickError::new)
                    }
                }
            }
            ContractExpression::Let {
                name,
                c_type,
                value,
                body,
            } => {
                let value = self.lower_requirement_value(value)?;
                let value =
                    checked_contract_let_value(value, *c_type, name).map_err(ClickError::new)?;
                let outer_values = self.values.clone();
                self.values.insert(name.clone(), value);
                let body_value = self.lower_requirement_value(body);
                self.values = outer_values;
                body_value
            }
            ContractExpression::Call { name, arguments } => {
                let state = CState::new().with_memory(self.memory.clone());
                evaluate_click_function_call(
                    &self.click_function_environment.clone(),
                    name,
                    arguments,
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &Assumptions::new(),
                    &self.predicate_environment.clone(),
                    &mut self.active_functions,
                )
                .map_err(ClickError::new)
            }
        }
    }

    fn lower_requirement_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CValue, ClickError> {
        match expression {
            CExpression::Value(value) => Ok(value.clone()),
            CExpression::Variable(name) => {
                self.values.get(name).cloned().ok_or_else(|| {
                    ClickError::new(format!("unknown requirement variable `{name}`"))
                })
            }
            CExpression::Add(left, right) => lower_contract_add(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Subtract(left, right) => lower_contract_subtract(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Multiply(left, right) => lower_contract_multiply(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Divide(left, right) => lower_contract_divide(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Remainder(left, right) => lower_contract_remainder(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::ShiftLeft(left, right) => lower_contract_shift_left(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::ShiftRight(left, right) => lower_contract_shift_right(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::BitwiseAnd(left, right) => lower_contract_bitwise_binary(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
                "&",
                bitvector32_and,
            ),
            CExpression::BitwiseOr(left, right) => lower_contract_bitwise_binary(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
                "|",
                bitvector32_or,
            ),
            CExpression::BitwiseXor(left, right) => lower_contract_bitwise_binary(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
                "^",
                bitvector32_xor,
            ),
            CExpression::BitwiseNot(expression) => {
                lower_contract_bitwise_not(self.lower_requirement_c_expression(expression)?)
            }
            CExpression::Load(pointer) => {
                let pointer = self.lower_requirement_c_expression(pointer)?;
                let CValue::Pointer(pointer) = pointer else {
                    return Err(ClickError::new("field load base is not a pointer"));
                };
                evaluate_contract_memory_load_from_memory(
                    &self.memory,
                    pointer,
                    CType::Int32,
                    &Assumptions::new(),
                )
                .map_err(ClickError::new)
            }
            _ => Err(ClickError::new(format!(
                "unsupported expression in `requires` proposition: `{expression:?}`"
            ))),
        }
    }
}

fn comparison_proposition(
    left: CValue,
    operator: ComparisonOperator,
    right: CValue,
) -> Result<Proposition, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        let Some((condition, value)) = comparison_condition(left_term, operator, right_term) else {
            return Err(ClickError::new("unsupported proposition comparison"));
        };
        Ok(Proposition::ConditionIs(condition, value))
    } else {
        Err(ClickError::new(format!(
            "cannot compare `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

fn proposition_as_single_condition(proposition: &Proposition) -> Option<(ConditionTerm, bool)> {
    match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Not(body) => {
            let Proposition::ConditionIs(condition, value) = body.as_ref() else {
                return None;
            };
            Some((condition.clone(), !*value))
        }
        _ => None,
    }
}

fn assumptions_prove_proposition_false(
    assumptions: &Assumptions,
    proposition: &Proposition,
) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !*value))
        }
        _ => assumptions.proves(&Proposition::Not(Box::new(proposition.clone()))),
    }
}

fn conditional_contract_value(
    proposition: &Proposition,
    then_value: CValue,
    else_value: CValue,
) -> Result<CValue, String> {
    if then_value == else_value {
        return Ok(then_value);
    }

    let Some((condition, expected)) = proposition_as_single_condition(proposition) else {
        return Err(
            "symbolic `if` expressions currently require a single comparison condition".to_string(),
        );
    };

    let (CValue::Int32(then_term), CValue::Int32(else_term)) = (then_value, else_value) else {
        return Err(
            "symbolic `if` expressions currently support only int32 branch values".to_string(),
        );
    };

    let (then_term, else_term) = if expected {
        (then_term, else_term)
    } else {
        (else_term, then_term)
    };
    Ok(CValue::Int32(Bitvector32Term::if_then_else(
        condition, then_term, else_term,
    )))
}

fn true_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(true), true)
}

fn false_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(false), true)
}

fn conjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => {
            false_proposition()
        }
        _ => Proposition::And(Box::new(left), Box::new(right)),
    }
}

fn disjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => true_proposition(),
        _ => Proposition::Or(Box::new(left), Box::new(right)),
    }
}

fn range_membership_proposition(
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
) -> Proposition {
    conjunction(
        Proposition::ConditionIs(signed_less_equal(start, item.clone()), true),
        Proposition::ConditionIs(signed_less_than(item, end), true),
    )
}

fn bounded_forall_int32(
    variable: Variable,
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
    body: Proposition,
) -> Proposition {
    Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(range_membership_proposition(start, item, end)),
            Box::new(body),
        )),
    }
}

fn bounded_exists_int32(
    name: String,
    variable: Variable,
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
    body: Proposition,
) -> Proposition {
    Proposition::Exists {
        name,
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(conjunction(
            range_membership_proposition(start, item, end),
            body,
        )),
    }
}

fn spec_range_membership_proposition(
    start: SpecExpression,
    item: SpecExpression,
    end: SpecExpression,
) -> SpecProposition {
    SpecProposition::And(
        Box::new(SpecProposition::Comparison {
            left: start,
            operator: CComparisonOperator::LessEqual,
            right: item.clone(),
        }),
        Box::new(SpecProposition::Comparison {
            left: item,
            operator: CComparisonOperator::LessThan,
            right: end,
        }),
    )
}

fn int32_term_value(value: CValue, label: &str) -> Result<Bitvector32Term, String> {
    let CValue::Int32(bits) = value else {
        return Err(format!("`{label}` is not int32"));
    };
    Ok(simp_bitvector(&bits))
}

fn promoted_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(bits) | CValue::UInt8(bits) => Some(simp_bitvector(bits)),
        CValue::Pointer(_) => None,
    }
}

fn concrete_fold_range(start: i32, end: i32) -> Result<std::ops::Range<i32>, String> {
    let length = i64::from(end) - i64::from(start);
    if length <= 0 {
        return Ok(start..start);
    }
    if length > MAX_CONCRETE_RANGE_FOLD_STEPS {
        return Err(format!(
            "`fold` range has {length} iterations; the current concrete unroll limit is {MAX_CONCRETE_RANGE_FOLD_STEPS}"
        ));
    }
    Ok(start..end)
}

fn concrete_bound_from_term(
    term: &Bitvector32Term,
    construct: &str,
    label: &str,
) -> Result<i32, String> {
    let term = simp_bitvector(term);
    let Bitvector32Term::Constant(value) = term else {
        return Err(format!(
            "symbolic `{construct}` {label} bounds are not supported yet"
        ));
    };
    Ok(value as i32)
}

fn fold_bound_variable(name: &str, salt: u64) -> Variable {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ salt;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x1000_0000_01b3);
    }
    Variable(3_000_000 + (hash % 1_000_000_000))
}

fn symbolic_range_fold_value(
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body_value: CValue,
) -> Result<CValue, String> {
    let initial = int32_term_value(initial, "fold initial value")?;
    let body = int32_term_value(body_value, "fold body value")?;
    Ok(CValue::Int32(Bitvector32Term::range_fold(
        start,
        end,
        initial,
        fold_bound_variable(accumulator, 0),
        fold_bound_variable(item, 1),
        body,
    )))
}

fn lower_contract_add(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_add(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| {
                ClickError::new(format!(
                    "cannot add pointer and `{offset:?}` in proposition"
                ))
            }),
        (offset, CValue::Pointer(pointer)) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| {
                ClickError::new(format!(
                    "cannot add `{offset:?}` and pointer in proposition"
                ))
            }),
        (left, right) => Err(ClickError::new(format!(
            "cannot add `{left:?}` and `{right:?}` in proposition"
        ))),
    }
}

fn lower_contract_subtract(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_subtract(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => {
            let Some(index) = promoted_int32_term(&offset) else {
                return Err(ClickError::new(format!(
                    "cannot subtract `{offset:?}` from pointer in proposition"
                )));
            };
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(ClickError::new(format!(
            "cannot subtract `{right:?}` from `{left:?}` in proposition"
        ))),
    }
}

fn lower_contract_multiply(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(bitvector32_multiply(left_term, right_term)))
    } else {
        Err(ClickError::new(format!(
            "cannot multiply `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

fn lower_contract_divide(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_divide(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot divide `{left:?}` by `{right:?}` in proposition"
        )))
    }
}

fn lower_contract_remainder(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_remainder(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot compute `{left:?}` % `{right:?}` in proposition"
        )))
    }
}

fn lower_contract_shift_left(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_left(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot apply `<<` to `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

fn lower_contract_shift_right(left: CValue, right: CValue) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_right(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot apply `>>` to `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

fn lower_contract_bitwise_binary(
    left: CValue,
    right: CValue,
    operator: &str,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(apply(left_term, right_term)))
    } else {
        Err(ClickError::new(format!(
            "cannot apply `{operator}` to `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

fn lower_contract_bitwise_not(value: CValue) -> Result<CValue, ClickError> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(ClickError::new(format!(
            "cannot apply `~` to `{value:?}` in proposition"
        )))
    }
}

fn bitvector32_add(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_add(*right))
        }
        (Bitvector32Term::Constant(constant), Bitvector32Term::Subtract(base, subtrahend))
            if subtrahend.as_ref() == &Bitvector32Term::Constant(*constant) =>
        {
            base.as_ref().clone()
        }
        (Bitvector32Term::Subtract(base, subtrahend), Bitvector32Term::Constant(constant))
            if subtrahend.as_ref() == &Bitvector32Term::Constant(*constant) =>
        {
            base.as_ref().clone()
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ => Bitvector32Term::Add(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_subtract(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        _ if left == right => Bitvector32Term::Constant(0),
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_addend => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_base.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_base => {
            bitvector32_subtract(left_base.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_addend => {
            bitvector32_subtract(left_base.as_ref().clone(), right_base.as_ref().clone())
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_base.as_ref() == &right => {
            left_addend.as_ref().clone()
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_addend.as_ref() == &right => {
            left_base.as_ref().clone()
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if &left == right_base.as_ref() => {
            bitvector32_subtract(Bitvector32Term::Constant(0), right_addend.as_ref().clone())
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if &left == right_addend.as_ref() => {
            bitvector32_subtract(Bitvector32Term::Constant(0), right_base.as_ref().clone())
        }
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_multiply(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_mul(*right))
        }
        (_, Bitvector32Term::Constant(1)) => left,
        (Bitvector32Term::Constant(1), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ => Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(0)) => Err("division by zero in proposition".to_string()),
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right))
            if *left == i32::MIN as u32 && *right == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => Ok(
            Bitvector32Term::Constant(((*left as i32) / (*right as i32)) as u32),
        ),
        (_, Bitvector32Term::Constant(1)) => Ok(left),
        _ => Ok(Bitvector32Term::Divide(Box::new(left), Box::new(right))),
    }
}

fn bitvector32_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(0)) => Err("division by zero in proposition".to_string()),
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right))
            if *left == i32::MIN as u32 && *right == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => Ok(
            Bitvector32Term::Constant(((*left as i32) % (*right as i32)) as u32),
        ),
        (_, Bitvector32Term::Constant(1)) => Ok(Bitvector32Term::Constant(0)),
        _ => Ok(Bitvector32Term::Remainder(Box::new(left), Box::new(right))),
    }
}

fn bitvector32_shift_count(right: u32) -> Option<u32> {
    let right = right as i32;
    (0..32).contains(&right).then_some(right as u32)
}

fn bitvector32_shift_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(right)) if bitvector32_shift_count(*right).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), _) if (*left as i32) < 0 => {
            Err("left shift of negative value in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            let count =
                bitvector32_shift_count(*right).expect("constant shift count was checked above");
            let shifted = ((*left as i32) as i64) << count;
            if shifted > i64::from(i32::MAX) {
                Err("signed left shift overflow in proposition".to_string())
            } else {
                Ok(Bitvector32Term::Constant((shifted as i32) as u32))
            }
        }
        _ => Ok(Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right))),
    }
}

fn bitvector32_shift_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(right)) if bitvector32_shift_count(*right).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            let count =
                bitvector32_shift_count(*right).expect("constant shift count was checked above");
            Ok(Bitvector32Term::Constant(((*left as i32) >> count) as u32))
        }
        (_, Bitvector32Term::Constant(0)) => Ok(left),
        _ => Ok(Bitvector32Term::ArithmeticShiftRight(
            Box::new(left),
            Box::new(right),
        )),
    }
}

fn bitvector32_and(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left & *right)
        }
        (_, Bitvector32Term::Constant(u32::MAX)) => left,
        (Bitvector32Term::Constant(u32::MAX), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ if left == right => left,
        _ => Bitvector32Term::BitwiseAnd(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_or(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left | *right)
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        (_, Bitvector32Term::Constant(u32::MAX)) | (Bitvector32Term::Constant(u32::MAX), _) => {
            Bitvector32Term::Constant(u32::MAX)
        }
        _ if left == right => left,
        _ => Bitvector32Term::BitwiseOr(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_xor(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left ^ *right)
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ if left == right => Bitvector32Term::Constant(0),
        _ => Bitvector32Term::BitwiseXor(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_not(value: Bitvector32Term) -> Bitvector32Term {
    match value {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(!value),
        Bitvector32Term::BitwiseNot(inner) => *inner,
        value => Bitvector32Term::BitwiseNot(Box::new(value)),
    }
}

fn signed_less_than(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) < (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
    }
}

fn signed_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) <= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
    }
}

fn signed_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) > (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
    }
}

fn signed_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) >= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
    }
}

fn bitvector32_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant(left == right)
        }
        _ => ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
    }
}

fn check_function_claim(
    claim_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    match claim {
        FunctionClaimRef::Ensure(_, ensure_clause) => match ensure_clause.ensure() {
            Ensure::Proposition(proposition) => prove_ensure_proposition(
                claim_label,
                path_index,
                path_facts,
                available_propositions,
                proposition,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )?,
            Ensure::Resource(resource) => prove_ensure_resource(
                claim_label,
                path_index,
                path_facts,
                available_propositions,
                resource,
                parameters,
                arguments,
                pre_state,
                outcome,
            )?,
        },
        FunctionClaimRef::Effect(_, effect_clause) => prove_effect_clause(
            claim_label,
            path_index,
            path_facts,
            available_propositions,
            effect_clause.effect(),
            parameters,
            arguments,
            pre_state,
            outcome,
        )?,
    }

    Ok(())
}

fn check_function_claim_by_simp(
    claim_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    match claim {
        FunctionClaimRef::Ensure(_, ensure_clause) => match ensure_clause.ensure() {
            Ensure::Proposition(proposition) => prove_ensure_proposition_by_simp(
                claim_label,
                path_index,
                path_facts,
                available_propositions,
                proposition,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            ),
            Ensure::Resource(resource) => prove_ensure_resource(
                claim_label,
                path_index,
                path_facts,
                available_propositions,
                resource,
                parameters,
                arguments,
                pre_state,
                outcome,
            ),
        },
        FunctionClaimRef::Effect(_, _) => Err(ClickError::new(format!(
            "`simp` does not prove effect clauses for `{claim_label}`; use `by frame;` or `by auto;`"
        ))),
    }
}

fn prove_ensure_resource(
    claim_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let CFunctionOutcome::Return {
        state: post_state, ..
    } = outcome
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}\n  path facts: {}",
            describe_function_outcome(outcome, parameters, arguments),
            describe_facts(path_facts)
        )));
    };
    let expected = lower_resource_clause(resource, parameters, arguments, pre_state.memory())?;
    let assumptions = assumptions_from_propositions(available_propositions);
    if post_state.resources().satisfies(&expected, &assumptions) {
        return Ok(());
    }
    Err(ClickError::new(format!(
        "`{claim_label}` failed on path {path_index}: missing resource `{}`\n  final resources: {}\n  path facts: {}",
        describe_resource(&expected, parameters, arguments),
        describe_resources(post_state.resources().resources(), parameters, arguments),
        describe_facts(path_facts)
    )))
}

fn check_function_claim_with_existence_steps(
    claim_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &mut Vec<Proposition>,
    claim: &FunctionClaimRef<'_>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proof_steps: &[ProofStep],
    original_requirements: &[Requirement],
    use_simp: bool,
) -> Result<(), ClickError> {
    let FunctionClaimRef::Ensure(_, ensure_clause) = claim else {
        return Err(ClickError::new(format!(
            "`witness` and `choose` proof steps currently prove proposition `ensures` clauses for `{claim_label}`; use `frame` for effect clauses"
        )));
    };
    let Ensure::Proposition(surface_goal) = ensure_clause.ensure() else {
        return Err(ClickError::new(format!(
            "`witness` and `choose` proof steps currently prove proposition `ensures` clauses for `{claim_label}`; resource `ensures` are checked directly"
        )));
    };
    let CFunctionOutcome::Return {
        value: result,
        state: post_state,
    } = outcome
    else {
        return Err(ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {}\n  path facts: {}",
            describe_function_outcome(outcome, parameters, arguments),
            describe_facts(path_facts)
        )));
    };

    let mut values = parameter_values(parameters, arguments).map_err(|error| {
        ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {}",
            error.message
        ))
    })?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let mut assumptions = assumptions_from_propositions(available_propositions);
    let mut next_lowering_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    let mut goal = lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        surface_goal,
        &mut next_lowering_variable,
        predicate_environment,
        click_function_environment,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: could not lower goal: {message}"
        ))
    })?;

    let mut next_choice_variable = 3_000_000;
    for (step_index, step) in proof_steps.iter().enumerate() {
        match step {
            ProofStep::Choose(choice) => {
                apply_choose_step(
                    choice,
                    claim_label,
                    path_index,
                    step_index,
                    available_propositions,
                    &mut values,
                    original_requirements,
                    &mut next_choice_variable,
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                )?;
                *available_propositions = unfold_available_predicate_facts(
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                    available_propositions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: {message}"
                    ))
                })?;
            }
            ProofStep::Witness(witness) => {
                assumptions = assumptions_from_propositions(available_propositions);
                goal = unfold_predicates_in_proposition(
                    predicate_environment,
                    click_function_environment,
                    unfolded_predicates,
                    &goal,
                    &assumptions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`witness` failed for `{claim_label}` path {path_index}, proof step {step_index}: {message}"
                    ))
                })?;
                let witness_value = evaluate_witness_step_value(
                    witness,
                    claim_label,
                    path_index,
                    step_index,
                    &values,
                    &array_refs,
                    pre_state,
                    post_state,
                    result,
                    &assumptions,
                    predicate_environment,
                    click_function_environment,
                )?;
                goal = apply_witness_step(
                    witness,
                    witness_value,
                    goal,
                    claim_label,
                    path_index,
                    step_index,
                )?;
            }
            _ => {}
        }
    }

    assumptions = assumptions_from_propositions(available_propositions);
    goal = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &goal,
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: {message}"
        ))
    })?;

    if use_simp {
        match simp_proposition(&goal, &assumptions) {
            SimpProposition::True => Ok(()),
            simplified => Err(ClickError::new(format!(
                "`witness`/`choose` failed for `{claim_label}` path {path_index}: simplified proposition was not true: {simplified:?}\n  instantiated goal: {goal:?}\n  path facts: {}",
                describe_facts(path_facts)
            ))),
        }
    } else if assumptions.proves(&goal) {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "`witness`/`choose` failed for `{claim_label}` path {path_index}: instantiated goal was not provable: {goal:?}\n  path facts: {}",
            describe_facts(path_facts)
        )))
    }
}

fn apply_choose_step(
    choice: &ProofChoice,
    claim_label: &str,
    path_index: usize,
    step_index: usize,
    available_propositions: &mut Vec<Proposition>,
    values: &mut BTreeMap<String, CValue>,
    original_requirements: &[Requirement],
    next_choice_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    if choice.name == "result" || values.contains_key(&choice.name) {
        return Err(ClickError::new(format!(
            "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: `{}` is already in scope",
            choice.name
        )));
    }

    let source_index = match &choice.source {
        ProofFactSource::Requirement(index) => {
            if *index >= original_requirements.len() {
                return Err(ClickError::new(format!(
                    "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: requirement {index} is out of range; function has {} requirement(s)",
                    original_requirements.len()
                )));
            }
            *index
        }
        ProofFactSource::RequirementLabel(label) => original_requirements
            .iter()
            .position(|requirement| requirement.label() == Some(label.as_str()))
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: unknown requirement label `{label}`"
                ))
            })?,
    };
    let mut source = available_propositions
        .get(source_index)
        .cloned()
        .ok_or_else(|| {
            ClickError::new(format!(
                "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: requirement {source_index} was not available"
            ))
        })?;
    if !matches!(source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty() {
        let assumptions = assumptions_from_propositions(available_propositions);
        source = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            &source,
            &assumptions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: {message}"
            ))
        })?;
    }

    let Proposition::Exists {
        var, sort, body, ..
    } = source
    else {
        return Err(ClickError::new(format!(
            "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: source is not an existential proposition"
        )));
    };
    if sort != Sort::CInt32 {
        return Err(ClickError::new(format!(
            "`choose` failed for `{claim_label}` path {path_index}, proof step {step_index}: only int32 existential choices are supported"
        )));
    }

    let chosen = Bitvector32Term::Variable(Variable(*next_choice_variable));
    *next_choice_variable += 1;
    values.insert(choice.name.clone(), CValue::Int32(chosen.clone()));
    available_propositions.push(substitute_int32_variable_in_proposition(&body, var, chosen));
    Ok(())
}

fn evaluate_witness_step_value(
    witness: &ProofWitness,
    claim_label: &str,
    path_index: usize,
    step_index: usize,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Bitvector32Term, ClickError> {
    let mut active_functions = BTreeSet::new();
    let value = evaluate_contract_expression_with_environment(
        values,
        array_refs,
        pre_state,
        post_state,
        Some(result),
        assumptions,
        &witness.value,
        predicate_environment,
        click_function_environment,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, proof step {step_index}: could not evaluate witness value for `{}`: {message}",
            witness.name
        ))
    })?;
    let CValue::Int32(value) = value else {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, proof step {step_index}: witness `{}` did not evaluate to int32",
            witness.name
        )));
    };
    Ok(value)
}

fn apply_witness_step(
    witness: &ProofWitness,
    witness_value: Bitvector32Term,
    goal: Proposition,
    claim_label: &str,
    path_index: usize,
    step_index: usize,
) -> Result<Proposition, ClickError> {
    let Proposition::Exists {
        name,
        var,
        sort,
        body,
    } = goal
    else {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, proof step {step_index}: goal is not an existential proposition"
        )));
    };
    if sort != Sort::CInt32 {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, proof step {step_index}: only int32 existential witnesses are supported"
        )));
    }
    if name != witness.name {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, proof step {step_index}: goal binds `{name}`, but proof provided witness `{}`",
            witness.name
        )));
    }

    Ok(substitute_int32_variable_in_proposition(
        &body,
        var,
        witness_value,
    ))
}

fn prove_ensure_proposition_by_simp(
    ensure_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Err(ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: {}\n  path facts: {}",
            describe_function_outcome(outcome, parameters, arguments),
            describe_facts(path_facts)
        )));
    };
    let mut proposition = lower_outcome_proposition(
        parameters,
        arguments,
        pre_state,
        state,
        value,
        available_propositions,
        proposition,
        predicate_environment,
        click_function_environment,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: could not lower proposition: {message}"
        ))
    })?;
    let assumptions = assumptions_from_propositions(available_propositions);
    proposition = unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &proposition,
        &assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: {message}"
        ))
    })?;
    match simp_proposition(&proposition, &assumptions) {
        SimpProposition::True => Ok(()),
        simplified => Err(ClickError::new(format!(
            "`simp` failed for `{ensure_label}` path {path_index}: simplified proposition was not true: {simplified:?}\n  original proposition: {proposition:?}\n  path facts: {}",
            describe_facts(path_facts)
        ))),
    }
}

fn unfold_available_predicate_facts(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    available_propositions: &[Proposition],
) -> Result<Vec<Proposition>, String> {
    if unfolded_predicates.is_empty() {
        return Ok(available_propositions.to_vec());
    }

    let assumptions = assumptions_from_propositions(available_propositions);
    let mut propositions = available_propositions.to_vec();
    for proposition in available_propositions {
        let unfolded = unfold_predicates_in_proposition(
            predicate_environment,
            click_function_environment,
            unfolded_predicates,
            proposition,
            &assumptions,
        )?;
        if &unfolded != proposition && !propositions.contains(&unfolded) {
            propositions.push(unfolded);
        }
    }
    Ok(propositions)
}

fn unfold_predicates_in_proposition(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> Result<Proposition, String> {
    let mut active = BTreeSet::new();
    unfold_predicates_in_proposition_with_active(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        proposition,
        assumptions,
        &mut active,
    )
}

fn unfold_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
    proposition: &Proposition,
    assumptions: &Assumptions,
    active: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        Proposition::Predicate { name, arguments }
            if unfolded_predicates
                .iter()
                .any(|predicate| predicate == name) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_predicate_definition(
                definition,
                arguments,
                assumptions,
                predicate_environment,
                click_function_environment,
            )?;
            let unfolded = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &unfolded,
                assumptions,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        Proposition::And(left, right) => Ok(Proposition::And(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Not(body) => Ok(Proposition::Not(Box::new(
            unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?,
        ))),
        Proposition::Implies(left, right) => {
            let left = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                left,
                assumptions,
                active,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                right,
                &right_assumptions,
                active,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        Proposition::ForAll { var, sort, body } => Ok(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Ok(Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                body,
                assumptions,
                active,
            )?),
        }),
        _ => Ok(proposition.clone()),
    }
}

fn instantiate_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[Term],
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let (memory, mut values, array_refs) = decode_predicate_arguments(definition, arguments)?;

    let mut next_variable = 2_500_000;
    let mut active_functions = BTreeSet::new();
    lower_predicate_body_proposition_with_environment(
        &mut values,
        &array_refs,
        &memory,
        assumptions,
        definition.body(),
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &mut active_functions,
    )
}

fn decode_predicate_arguments(
    definition: &PredicateDefinition,
    arguments: &[Term],
) -> Result<(CMemory, BTreeMap<String, CValue>, ClickArrayRefs), String> {
    let expanded_len = definition
        .parameters()
        .iter()
        .map(|parameter| {
            if parameter_is_click_array_ref(parameter) {
                2
            } else {
                1
            }
        })
        .sum::<usize>();

    if arguments.len() == expanded_len {
        let mut values = BTreeMap::new();
        let mut array_refs = BTreeMap::new();
        let mut default_memory = None;
        let mut index = 0;
        for parameter in definition.parameters() {
            if parameter_is_click_array_ref(parameter) {
                let Some(Term::CMemory(memory)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref memory",
                        definition.name(),
                        parameter.name()
                    ));
                };
                let Some(Term::CValue(CValue::Pointer(pointer))) = arguments.get(index + 1) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                default_memory.get_or_insert_with(|| memory.clone());
                values.insert(
                    parameter.name().to_string(),
                    CValue::Pointer(pointer.clone()),
                );
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        memory: memory.clone(),
                        pointer: pointer.clone(),
                        element_type: click_array_element_type(parameter.c_type()).ok_or_else(
                            || {
                                format!(
                                    "predicate `{}` argument `{}` is not an array-ref parameter",
                                    definition.name(),
                                    parameter.name()
                                )
                            },
                        )?,
                    },
                );
                index += 2;
            } else {
                let Some(Term::CValue(value)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` did not lower to a C value",
                        definition.name(),
                        parameter.name()
                    ));
                };
                values.insert(parameter.name().to_string(), value.clone());
                index += 1;
            }
        }
        return Ok((default_memory.unwrap_or_default(), values, array_refs));
    }

    if arguments.len() == definition.parameters().len() + 1 {
        let Term::CMemory(memory) = &arguments[0] else {
            return Err(format!(
                "predicate `{}` is missing its legacy hidden memory argument",
                definition.name()
            ));
        };
        let mut values = BTreeMap::new();
        let mut array_refs = BTreeMap::new();
        for (parameter, argument) in definition.parameters().iter().zip(&arguments[1..]) {
            let Term::CValue(value) = argument else {
                return Err(format!(
                    "predicate `{}` argument `{}` did not lower to a C value",
                    definition.name(),
                    parameter.name()
                ));
            };
            if parameter_is_click_array_ref(parameter) {
                let CValue::Pointer(pointer) = value else {
                    return Err(format!(
                        "predicate `{}` argument `{}` did not lower to a pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        memory: memory.clone(),
                        pointer: pointer.clone(),
                        element_type: click_array_element_type(parameter.c_type()).ok_or_else(
                            || {
                                format!(
                                    "predicate `{}` argument `{}` is not an array-ref parameter",
                                    definition.name(),
                                    parameter.name()
                                )
                            },
                        )?,
                    },
                );
            }
            values.insert(parameter.name().to_string(), value.clone());
        }
        return Ok((memory.clone(), values, array_refs));
    }

    Err(format!(
        "predicate `{}` has malformed lowered argument count: expected {} expanded argument term(s), or legacy hidden memory plus {} argument(s), got {}",
        definition.name(),
        expanded_len,
        definition.parameters().len(),
        arguments.len()
    ))
}

fn lower_predicate_body_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    assumptions: &Assumptions,
    proposition: &ClickProposition,
    next_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            comparison_proposition(left, *operator, right).map_err(|error| error.message)
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
            Box::new(lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?,
        ))),
        ClickProposition::Implies(left, right) => {
            let left = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                &right_assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        ClickProposition::ForAll { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `forall (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::ForAll {
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `exists (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::Exists {
                name: name.clone(),
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `all` start bound",
            )?;
            let end = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `all` end bound",
            )?;
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let item_bits = Bitvector32Term::Variable(variable);
            let item_value = CValue::Int32(item_bits.clone());
            let outer_values = values.clone();
            values.insert(item.clone(), item_value.clone());
            let body_assumptions =
                assumptions
                    .clone()
                    .assume_proposition(range_membership_proposition(
                        start.clone(),
                        item_bits.clone(),
                        end.clone(),
                    ));
            let body = match lower_predicate_body_proposition_with_environment(
                values,
                array_refs,
                memory,
                &body_assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            ) {
                Ok(body) => body,
                Err(error) => {
                    *values = outer_values;
                    return Err(error);
                }
            };
            *values = outer_values;
            Ok(bounded_forall_int32(variable, start, item_bits, end, body))
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `any` start bound",
            )?;
            let end = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `any` end bound",
            )?;
            let outer_values = values.clone();
            match (
                concrete_bound_from_term(&start, "any", "start"),
                concrete_bound_from_term(&end, "any", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    let mut proposition = false_proposition();
                    for index in concrete_fold_range(start, end)? {
                        *values = outer_values.clone();
                        values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        let body = match lower_predicate_body_proposition_with_environment(
                            values,
                            array_refs,
                            memory,
                            assumptions,
                            body,
                            next_variable,
                            predicate_environment,
                            click_function_environment,
                            active_functions,
                        ) {
                            Ok(body) => body,
                            Err(error) => {
                                *values = outer_values;
                                return Err(error);
                            }
                        };
                        proposition = disjunction(proposition, body);
                    }
                    *values = outer_values;
                    Ok(proposition)
                }
                _ => {
                    let variable = Variable(*next_variable);
                    *next_variable += 1;
                    let item_bits = Bitvector32Term::Variable(variable);
                    let item_value = CValue::Int32(item_bits.clone());
                    values.insert(item.clone(), item_value.clone());
                    let body_assumptions =
                        assumptions
                            .clone()
                            .assume_proposition(range_membership_proposition(
                                start.clone(),
                                item_bits.clone(),
                                end.clone(),
                            ));
                    let body = match lower_predicate_body_proposition_with_environment(
                        values,
                        array_refs,
                        memory,
                        &body_assumptions,
                        body,
                        next_variable,
                        predicate_environment,
                        click_function_environment,
                        active_functions,
                    ) {
                        Ok(body) => body,
                        Err(error) => {
                            *values = outer_values;
                            return Err(error);
                        }
                    };
                    *values = outer_values;
                    Ok(bounded_exists_int32(
                        item.clone(),
                        variable,
                        start,
                        item_bits,
                        end,
                        body,
                    ))
                }
            }
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let state = CState::new().with_memory(memory.clone());
            let lowered_arguments = lower_predicate_call_arguments_with_environment(
                definition,
                arguments,
                values,
                array_refs,
                &state,
                &state,
                None,
                assumptions,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            Ok(Proposition::Predicate {
                name: name.clone(),
                arguments: lowered_arguments,
            })
        }
    }
}

fn evaluate_predicate_contract_expression(
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    let state = CState::new().with_memory(memory.clone());
    match expression {
        ContractExpression::CFragment(expression) => {
            evaluate_c_contract_expression(values, &state, None, assumptions, expression)
        }
        ContractExpression::Old(_) => {
            Err("`old(...)` is not available in predicate definitions".to_string())
        }
        ContractExpression::At { .. } => {
            Err("`at(...)` is not available in predicate definitions".to_string())
        }
        ContractExpression::Add(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_add(left, right)
        }
        ContractExpression::Subtract(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        ContractExpression::Multiply(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        ContractExpression::Divide(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        ContractExpression::Remainder(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        ContractExpression::ShiftRight(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        ContractExpression::BitwiseOr(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        ContractExpression::BitwiseXor(left, right) => {
            let left = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        ContractExpression::BitwiseNot(expression) => {
            let value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        ContractExpression::Index(base, index) => {
            if contains_old_expression(base) {
                return Err("`old(...)` is not available in predicate definitions".to_string());
            }
            if contains_at_expression(base) {
                return Err("`at(...)` is not available in predicate definitions".to_string());
            }
            let array_ref = evaluate_contract_array_ref_with_environment(
                values,
                array_refs,
                &state,
                &state,
                None,
                assumptions,
                base,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let index = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                index,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let CValue::Int32(index) = index else {
                return Err(format!(
                    "array index did not evaluate to int32: `{index:?}`"
                ));
            };
            let element_type = array_ref.element_type;
            let pointer =
                offset_pointer_by_elements(array_ref.pointer, index, element_type.byte_width());
            evaluate_contract_memory_load_from_memory(
                &array_ref.memory,
                pointer,
                element_type,
                assumptions,
            )
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut condition_values = values.clone();
            let mut next_variable = 2_500_000;
            let condition = lower_predicate_body_proposition_with_environment(
                &mut condition_values,
                array_refs,
                memory,
                assumptions,
                condition,
                &mut next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            if assumptions.proves(&condition) {
                return evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    then_branch,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                );
            }
            if assumptions_prove_proposition_false(assumptions, &condition) {
                return evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    else_branch,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                );
            }

            let then_value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                then_branch,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let else_value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                else_branch,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            conditional_contract_value(&condition, then_value, else_value)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "fold start",
            )?;
            let end = int32_term_value(
                evaluate_predicate_contract_expression(
                    values,
                    array_refs,
                    memory,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "fold end",
            )?;
            let mut value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                initial,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            match (
                concrete_bound_from_term(&start, "fold", "start"),
                concrete_bound_from_term(&end, "fold", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    for index in concrete_fold_range(start, end)? {
                        let mut fold_values = values.clone();
                        fold_values.insert(accumulator.clone(), value);
                        fold_values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        value = evaluate_predicate_contract_expression(
                            &fold_values,
                            array_refs,
                            memory,
                            assumptions,
                            body,
                            predicate_environment,
                            click_function_environment,
                            active_functions,
                        )?;
                    }
                    Ok(value)
                }
                _ => {
                    let mut fold_values = values.clone();
                    fold_values.insert(
                        accumulator.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                            accumulator,
                            0,
                        ))),
                    );
                    fold_values.insert(
                        item.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                    );
                    let body_value = evaluate_predicate_contract_expression(
                        &fold_values,
                        array_refs,
                        memory,
                        assumptions,
                        body,
                        predicate_environment,
                        click_function_environment,
                        active_functions,
                    )?;
                    symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                }
            }
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value = evaluate_predicate_contract_expression(
                values,
                array_refs,
                memory,
                assumptions,
                value,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let value = checked_contract_let_value(value, *c_type, name)?;
            let mut let_values = values.clone();
            let_values.insert(name.clone(), value);
            evaluate_predicate_contract_expression(
                &let_values,
                array_refs,
                memory,
                assumptions,
                body,
                predicate_environment,
                click_function_environment,
                active_functions,
            )
        }
        ContractExpression::Call { name, arguments } => evaluate_click_function_call(
            click_function_environment,
            name,
            arguments,
            values,
            array_refs,
            &state,
            &state,
            None,
            assumptions,
            predicate_environment,
            active_functions,
        ),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SimpProposition {
    True,
    False,
    Proposition(Proposition),
}

fn simp_proposition(proposition: &Proposition, assumptions: &Assumptions) -> SimpProposition {
    match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition(condition, assumptions) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match simp_proposition(body, assumptions) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::ForAll { .. }
        | Proposition::Exists { .. }
        | Proposition::Predicate { .. }
        | Proposition::CExpressionEvaluates { .. }
        | Proposition::CStatementExecutes { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CMemoryCanLoad { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CMemoryValidRange { .. }
        | Proposition::CMemoryDisjoint { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CWhileInvariantRule { .. } => {
            if assumptions.proves(proposition) {
                SimpProposition::True
            } else {
                SimpProposition::Proposition(proposition.clone())
            }
        }
    }
}

impl SimpProposition {
    fn into_proposition(self) -> Proposition {
        match self {
            Self::True => Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            Self::False => Proposition::ConditionIs(ConditionTerm::Constant(false), true),
            Self::Proposition(proposition) => proposition,
        }
    }
}

fn simp_terms_equal(left: &Term, right: &Term) -> Option<bool> {
    let left = simp_term(left);
    let right = simp_term(right);
    if left == right {
        return Some(true);
    }
    match (&left, &right) {
        (Term::Bitvector32(left), Term::Bitvector32(right)) => Some(
            simp_bitvector_const(&simp_bitvector(left))?
                == simp_bitvector_const(&simp_bitvector(right))?,
        ),
        (Term::Condition(left), Term::Condition(right)) => Some(
            simp_condition_without_assumptions(left)? == simp_condition_without_assumptions(right)?,
        ),
        _ => None,
    }
}

fn simp_term(term: &Term) -> Term {
    match term {
        Term::Condition(condition) => match simp_condition_without_assumptions(condition) {
            Some(value) => Term::Condition(ConditionTerm::Constant(value)),
            None => term.clone(),
        },
        Term::Bitvector32(term) => Term::Bitvector32(simp_bitvector(term)),
        Term::CValue(CValue::Int32(term)) => Term::CValue(CValue::Int32(simp_bitvector(term))),
        _ => term.clone(),
    }
}

fn simp_condition(condition: &ConditionTerm, assumptions: &Assumptions) -> Option<bool> {
    simp_condition_without_assumptions(condition).or_else(|| {
        assumptions
            .proves(&Proposition::ConditionIs(condition.clone(), true))
            .then_some(true)
            .or_else(|| {
                assumptions
                    .proves(&Proposition::ConditionIs(condition.clone(), false))
                    .then_some(false)
            })
    })
}

fn simp_condition_without_assumptions(condition: &ConditionTerm) -> Option<bool> {
    match condition {
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::Bitvector32Equal(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(simp_bitvector_const(&left)? == simp_bitvector_const(&right)?)
            }
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) < (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) <= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) > (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) >= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Variable(_)
        | ConditionTerm::Bitvector32SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _)
        | ConditionTerm::PointerOffsetEqual(_, _) => None,
    }
}

fn simp_bitvector_const(term: &Bitvector32Term) -> Option<u32> {
    match term {
        Bitvector32Term::Constant(value) => Some(*value),
        Bitvector32Term::Variable(_)
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::MemoryLoad(_, _) => None,
        Bitvector32Term::Add(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_add(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Subtract(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_sub(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Multiply(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_mul(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left / right) as u32)
            }
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left % right) as u32)
            }
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            if left < 0 {
                None
            } else {
                let shifted = (left as i64) << right;
                (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
            }
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            Some((left >> right) as u32)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            Some(simp_bitvector_const(left)? & simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            Some(simp_bitvector_const(left)? | simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            Some(simp_bitvector_const(left)? ^ simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseNot(value) => Some(!simp_bitvector_const(value)?),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition)? {
            true => simp_bitvector_const(then_term),
            false => simp_bitvector_const(else_term),
        },
    }
}

fn simp_bitvector(term: &Bitvector32Term) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::Add(left, right) => {
            bitvector32_add(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Subtract(left, right) => {
            bitvector32_subtract(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Multiply(left, right) => {
            bitvector32_multiply(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_divide(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Divide(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_remainder(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Remainder(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_left(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_right(left.clone(), right.clone()).unwrap_or_else(|_| {
                Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
            })
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            bitvector32_and(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            bitvector32_or(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            bitvector32_xor(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseNot(value) => bitvector32_not(simp_bitvector(value)),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition) {
            Some(true) => simp_bitvector(then_term),
            Some(false) => simp_bitvector(else_term),
            None => Bitvector32Term::if_then_else(
                condition.as_ref().clone(),
                simp_bitvector(then_term),
                simp_bitvector(else_term),
            ),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::range_fold(
            simp_bitvector(start),
            simp_bitvector(end),
            simp_bitvector(initial),
            *accumulator,
            *item,
            simp_bitvector(body),
        ),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone())
        }
    }
}

fn prove_effect_clause(
    claim_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    effect: &Effect,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let CFunctionOutcome::Return { value: _, state } = outcome else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}\n  path facts: {}",
            describe_function_outcome(outcome, parameters, arguments),
            describe_facts(path_facts)
        )));
    };
    prove_mutation_footprint(
        claim_label,
        path_index,
        path_facts,
        available_propositions,
        parameters,
        arguments,
        pre_state,
        state,
        effect,
    )
}

fn prove_ensure_proposition(
    ensure_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    unfolded_predicates: &[String],
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let comparison = format!(
                "{} {operator} {}",
                describe_contract_expression(left),
                describe_contract_expression(right)
            );
            match outcome {
                CFunctionOutcome::Return { value, state } => {
                    let left_value = evaluate_contract_expression(
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        value,
                        available_propositions,
                        left,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: could not evaluate left side: {message}"
                        ))
                    })?;
                    let right_value = evaluate_contract_expression(
                        parameters,
                        arguments,
                        pre_state,
                        state,
                        value,
                        available_propositions,
                        right,
                        predicate_environment,
                        click_function_environment,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: could not evaluate right side: {message}"
                        ))
                    })?;
                    prove_value_comparison(
                        &left_value,
                        *operator,
                        &right_value,
                        available_propositions,
                    )
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: left side evaluated to {}, right side evaluated to {}\n  path facts: {}",
                            describe_c_value(&left_value, parameters, arguments),
                            describe_c_value(&right_value, parameters, arguments),
                            describe_facts(path_facts)
                        ))
                    })?;
                }
                other => {
                    return Err(ClickError::new(format!(
                        "`ensures {comparison}` failed for `{ensure_label}` path {path_index}: {}\n  path facts: {}",
                        describe_function_outcome(other, parameters, arguments),
                        describe_facts(path_facts)
                    )));
                }
            }
        }
        ClickProposition::And(left, right) => {
            prove_ensure_proposition(
                ensure_label,
                path_index,
                path_facts,
                available_propositions,
                left,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )?;
            prove_ensure_proposition(
                ensure_label,
                path_index,
                path_facts,
                available_propositions,
                right,
                parameters,
                arguments,
                pre_state,
                outcome,
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
            )?;
        }
        _ => {
            let surface_proposition = describe_click_proposition(proposition);
            let CFunctionOutcome::Return { value, state } = outcome else {
                return Err(ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {}\n  path facts: {}",
                    describe_function_outcome(outcome, parameters, arguments),
                    describe_facts(path_facts)
                )));
            };
            let mut proposition = lower_outcome_proposition(
                parameters,
                arguments,
                pre_state,
                state,
                value,
                available_propositions,
                proposition,
                predicate_environment,
                click_function_environment,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: could not lower proposition: {message}"
                ))
            })?;
            let assumptions = assumptions_from_propositions(available_propositions);
            proposition = unfold_predicates_in_proposition(
                predicate_environment,
                click_function_environment,
                unfolded_predicates,
                &proposition,
                &assumptions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: {message}"
                ))
            })?;
            if !assumptions.proves(&proposition) {
                return Err(ClickError::new(format!(
                    "`ensures {surface_proposition}` failed for `{ensure_label}` path {path_index}: proposition was not provable\n  path facts: {}",
                    describe_facts(path_facts)
                )));
            }
        }
    }
    Ok(())
}

fn prove_mutation_footprint(
    claim_label: &str,
    path_index: usize,
    path_facts: &[crate::kernel::PathFact],
    available_propositions: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    effect: &Effect,
) -> Result<(), ClickError> {
    let segments = match effect {
        Effect::Immutable => Vec::new(),
        Effect::Mutable(segments) => segments
            .iter()
            .map(|segment| {
                if segment.state != ContractSegmentState::Current {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` failed on path {path_index}: `mutable` expects current-state segments"
                    )));
                }
                evaluate_effect_segment(
                    parameters,
                    arguments,
                    pre_state,
                    available_propositions,
                    segment,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` failed on path {path_index}: could not evaluate mutable segment `{}`: {message}",
                        describe_contract_segment(segment)
                    ))
                })
            })
            .collect::<Result<Vec<_>, _>>()?,
    };
    let assumptions = assumptions_from_propositions(available_propositions);
    let mut writes = post_state
        .memory()
        .differing_cell_pointers(pre_state.memory())
        .into_iter()
        .filter(is_effect_relevant_pointer)
        .collect::<BTreeSet<_>>();
    writes.extend(
        path_facts
            .iter()
            .filter_map(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly { pointers, .. } => Some(pointers.as_slice()),
                _ => None,
            })
            .flatten()
            .cloned(),
    );
    writes.retain(is_effect_relevant_pointer);

    for pointer in &writes {
        if !segments
            .iter()
            .any(|segment| segment_contains_pointer(segment, pointer, &assumptions))
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` failed on path {path_index}: write to `{}` is outside the mutable footprint\n  mutable segments: {}\n  evaluated segments: {}\n  path facts: {}",
                describe_pointer(pointer, parameters, arguments),
                describe_contract_segments(&segments),
                describe_evaluated_segments(&segments),
                describe_facts(path_facts)
            )));
        }
    }

    let effect_summary_ranges = path_facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => {
                Some(mutable_ranges.as_slice())
            }
            _ => None,
        })
        .flatten()
        .filter(|range| is_effect_relevant_pointer(range.base()));

    for range in effect_summary_ranges {
        if !segments
            .iter()
            .any(|segment| segment_contains_range(segment, range, &assumptions))
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` failed on path {path_index}: effect summary range `{}` is outside the mutable footprint\n  mutable segments: {}\n  evaluated segments: {}\n  path facts: {}",
                describe_memory_range(range, parameters, arguments),
                describe_contract_segments(&segments),
                describe_evaluated_segments(&segments),
                describe_facts(path_facts)
            )));
        }
    }

    Ok(())
}

fn is_effect_relevant_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct EvaluatedContractSegment {
    source: ContractSegment,
    base: Pointer,
    start: Bitvector32Term,
    end: Bitvector32Term,
}

fn evaluate_effect_segment(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry_state: &CState,
    available_propositions: &[Proposition],
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err(
            "effect segments are already entry-state references; `old(...)` is not supported here"
                .to_string(),
        );
    }
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let assumptions = assumptions_from_propositions(available_propositions);
    let base = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.base,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.start,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.end,
    )?;
    let CValue::Int32(end) = end else {
        return Err("segment end did not evaluate to int32".to_string());
    };

    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base,
        start,
        end,
    })
}

fn evaluate_requirement_segment(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry_state: &CState,
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err(
            "requirement segments are entry-state references; `old(...)` is not supported here"
                .to_string(),
        );
    }
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let assumptions = Assumptions::new();
    let base = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.base,
    )?;
    let CValue::Pointer(base) = base else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let start = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.start,
    )?;
    let CValue::Int32(start) = start else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let end = evaluate_c_contract_expression(
        &parameter_values,
        entry_state,
        None,
        &assumptions,
        &segment.end,
    )?;
    let CValue::Int32(end) = end else {
        return Err("segment end did not evaluate to int32".to_string());
    };

    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base,
        start,
        end,
    })
}

fn segment_contains_pointer(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    let Some(index) = pointer_element_index_from_base(pointer, &segment.base) else {
        return false;
    };
    assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        signed_less_than(index, segment.end.clone()),
        true,
    ))
}

fn segment_contains_range(
    segment: &EvaluatedContractSegment,
    range: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    let Some(base_index) = pointer_element_index_from_base(range.base(), &segment.base) else {
        return false;
    };
    let range_start = bitvector32_add(base_index.clone(), range.start().clone());
    let range_end = bitvector32_add(base_index, range.end().clone());

    assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(segment.start.clone(), range_start),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(range_end, segment.end.clone()),
        true,
    ))
}

fn pointer_element_index_from_base(pointer: &Pointer, base: &Pointer) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return int32_element_index_from_pointer_offset(&pointer.offset);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            int32_element_index_from_pointer_offset(left)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                int32_element_index_from_pointer_offset(&pointer.offset),
                int32_element_index_from_pointer_offset(&base.offset),
            ) {
                Some(bitvector32_subtract(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

fn int32_element_index_from_pointer_offset(offset: &PointerOffsetTerm) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % 4 == 0 => {
            let index = offset / 4;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if *byte_width == 4 => {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            int32_element_index_from_pointer_offset(right)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            int32_element_index_from_pointer_offset(left)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            int32_element_index_from_pointer_offset(left)?,
            int32_element_index_from_pointer_offset(right)?,
        )),
        _ => None,
    }
}

fn prove_value_comparison(
    actual: &CValue,
    operator: ComparisonOperator,
    expected: &CValue,
    available_propositions: &[Proposition],
) -> Option<()> {
    let proposition = comparison_proposition(actual.clone(), operator, expected.clone()).ok()?;
    let assumptions = available_propositions
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition);
    assumptions.proves(&proposition).then_some(())
}

fn comparison_condition(
    actual: Bitvector32Term,
    operator: ComparisonOperator,
    expected: Bitvector32Term,
) -> Option<(ConditionTerm, bool)> {
    match operator {
        ComparisonOperator::Equal => Some((bitvector32_equal(actual, expected), true)),
        ComparisonOperator::NotEqual => Some((bitvector32_equal(actual, expected), false)),
        ComparisonOperator::LessThan => Some((signed_less_than(actual, expected), true)),
        ComparisonOperator::LessEqual => Some((signed_less_equal(actual, expected), true)),
        ComparisonOperator::GreaterThan => Some((signed_greater_than(actual, expected), true)),
        ComparisonOperator::GreaterEqual => Some((signed_greater_equal(actual, expected), true)),
    }
}

fn evaluate_contract_expression(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_propositions: &[Proposition],
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<CValue, String> {
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_propositions);
    let mut active_functions = BTreeSet::new();
    evaluate_contract_expression_with_environment(
        &parameter_values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        expression,
        predicate_environment,
        click_function_environment,
        &mut active_functions,
    )
}

fn lower_outcome_proposition(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    post_state: &CState,
    result: &CValue,
    available_propositions: &[Proposition],
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, String> {
    let mut values = parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &values, post_state.memory());
    let assumptions = assumptions_from_propositions(available_propositions);
    let mut next_variable = 2_000_000;
    let mut active_functions = BTreeSet::new();
    lower_outcome_proposition_with_environment(
        &mut values,
        &array_refs,
        pre_state,
        post_state,
        Some(result),
        &assumptions,
        proposition,
        &mut next_variable,
        predicate_environment,
        click_function_environment,
        &mut active_functions,
    )
}

fn lower_outcome_proposition_with_environment(
    values: &mut BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    proposition: &ClickProposition,
    next_variable: &mut u64,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = evaluate_contract_expression_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            comparison_proposition(left, *operator, right).map_err(|error| error.message)
        }
        ClickProposition::And(left, right) => Ok(Proposition::And(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
            Box::new(lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
            lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?,
        ))),
        ClickProposition::Implies(left, right) => {
            let left = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                &right_assumptions,
                right,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        ClickProposition::ForAll { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `forall (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::ForAll {
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            if *c_type != C0Type::Int32 {
                return Err("only `exists (int32 ...)` is supported".to_string());
            }
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let previous = values.insert(
                name.clone(),
                CValue::Int32(Bitvector32Term::Variable(variable)),
            );
            let body = lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            match previous {
                Some(value) => {
                    values.insert(name.clone(), value);
                }
                None => {
                    values.remove(name);
                }
            }
            Ok(Proposition::Exists {
                name: name.clone(),
                var: variable,
                sort: Sort::CInt32,
                body: Box::new(body),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `all` start bound",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `all` end bound",
            )?;
            let variable = Variable(*next_variable);
            *next_variable += 1;
            let item_bits = Bitvector32Term::Variable(variable);
            let item_value = CValue::Int32(item_bits.clone());
            let outer_values = values.clone();
            values.insert(item.clone(), item_value.clone());
            let body_assumptions =
                assumptions
                    .clone()
                    .assume_proposition(range_membership_proposition(
                        start.clone(),
                        item_bits.clone(),
                        end.clone(),
                    ));
            let body = match lower_outcome_proposition_with_environment(
                values,
                array_refs,
                pre_state,
                post_state,
                result,
                &body_assumptions,
                body,
                next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            ) {
                Ok(body) => body,
                Err(error) => {
                    *values = outer_values;
                    return Err(error);
                }
            };
            *values = outer_values;
            Ok(bounded_forall_int32(variable, start, item_bits, end, body))
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `any` start bound",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "range `any` end bound",
            )?;
            let outer_values = values.clone();
            match (
                concrete_bound_from_term(&start, "any", "start"),
                concrete_bound_from_term(&end, "any", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    let mut proposition = false_proposition();
                    for index in concrete_fold_range(start, end)? {
                        *values = outer_values.clone();
                        values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        let body = match lower_outcome_proposition_with_environment(
                            values,
                            array_refs,
                            pre_state,
                            post_state,
                            result,
                            assumptions,
                            body,
                            next_variable,
                            predicate_environment,
                            click_function_environment,
                            active_functions,
                        ) {
                            Ok(body) => body,
                            Err(error) => {
                                *values = outer_values;
                                return Err(error);
                            }
                        };
                        proposition = disjunction(proposition, body);
                    }
                    *values = outer_values;
                    Ok(proposition)
                }
                _ => {
                    let variable = Variable(*next_variable);
                    *next_variable += 1;
                    let item_bits = Bitvector32Term::Variable(variable);
                    let item_value = CValue::Int32(item_bits.clone());
                    values.insert(item.clone(), item_value.clone());
                    let body_assumptions =
                        assumptions
                            .clone()
                            .assume_proposition(range_membership_proposition(
                                start.clone(),
                                item_bits.clone(),
                                end.clone(),
                            ));
                    let body = match lower_outcome_proposition_with_environment(
                        values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        &body_assumptions,
                        body,
                        next_variable,
                        predicate_environment,
                        click_function_environment,
                        active_functions,
                    ) {
                        Ok(body) => body,
                        Err(error) => {
                            *values = outer_values;
                            return Err(error);
                        }
                    };
                    *values = outer_values;
                    Ok(bounded_exists_int32(
                        item.clone(),
                        variable,
                        start,
                        item_bits,
                        end,
                        body,
                    ))
                }
            }
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let lowered_arguments = if let Some(definition) = predicate_environment.get(name) {
                lower_predicate_call_arguments_with_environment(
                    definition,
                    arguments,
                    values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?
            } else {
                let mut lowered_arguments = vec![Term::CMemory(post_state.memory().clone())];
                lowered_arguments.extend(
                    arguments
                        .iter()
                        .map(|argument| {
                            evaluate_contract_expression_with_environment(
                                values,
                                array_refs,
                                pre_state,
                                post_state,
                                result,
                                assumptions,
                                argument,
                                predicate_environment,
                                click_function_environment,
                                active_functions,
                            )
                            .map(Term::CValue)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                );
                lowered_arguments
            };
            Ok(Proposition::Predicate {
                name: name.clone(),
                arguments: lowered_arguments,
            })
        }
    }
}

fn evaluate_contract_expression_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    match expression {
        ContractExpression::CFragment(expression) => evaluate_c_contract_expression(
            parameter_values,
            post_state,
            result,
            assumptions,
            expression,
        ),
        ContractExpression::Old(expression) => evaluate_contract_expression_with_environment(
            parameter_values,
            &array_refs_with_memory(array_refs, pre_state.memory()),
            pre_state,
            pre_state,
            None,
            assumptions,
            expression,
            predicate_environment,
            click_function_environment,
            active_functions,
        ),
        ContractExpression::At {
            selector,
            expression,
        } if visit_selector_is_function_entry(selector) => {
            evaluate_contract_expression_with_environment(
                parameter_values,
                &array_refs_with_memory(array_refs, pre_state.memory()),
                pre_state,
                pre_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )
        }
        ContractExpression::At { .. } => Err(
            "`at(...)` is currently supported in concrete evaluation only for `function.entry`"
                .to_string(),
        ),
        ContractExpression::Add(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_add(left, right)
        }
        ContractExpression::Subtract(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        ContractExpression::Multiply(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        ContractExpression::Divide(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        ContractExpression::Remainder(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        ContractExpression::ShiftRight(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        ContractExpression::BitwiseOr(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        ContractExpression::BitwiseXor(left, right) => {
            let left = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let right = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        ContractExpression::BitwiseNot(expression) => {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        ContractExpression::Index(base, index) => {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                base,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let index = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                index,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let CValue::Int32(index) = index else {
                return Err(format!(
                    "array index did not evaluate to int32: `{index:?}`"
                ));
            };
            let element_type = array_ref.element_type;
            let pointer =
                offset_pointer_by_elements(array_ref.pointer, index, element_type.byte_width());
            evaluate_contract_memory_load_from_memory(
                &array_ref.memory,
                pointer,
                element_type,
                assumptions,
            )
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut values = parameter_values.clone();
            let mut next_variable = 2_000_000;
            let condition = lower_outcome_proposition_with_environment(
                &mut values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                condition,
                &mut next_variable,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            if assumptions.proves(&condition) {
                return evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    then_branch,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                );
            }
            if assumptions_prove_proposition_false(assumptions, &condition) {
                return evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    else_branch,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                );
            }

            let then_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                then_branch,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let else_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                else_branch,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            conditional_contract_value(&condition, then_value, else_value)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = int32_term_value(
                evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    start,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "fold start",
            )?;
            let end = int32_term_value(
                evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    end,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?,
                "fold end",
            )?;
            let mut value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                initial,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            match (
                concrete_bound_from_term(&start, "fold", "start"),
                concrete_bound_from_term(&end, "fold", "end"),
            ) {
                (Ok(start), Ok(end)) => {
                    for index in concrete_fold_range(start, end)? {
                        let mut fold_values = parameter_values.clone();
                        fold_values.insert(accumulator.clone(), value);
                        fold_values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Constant(index as u32)),
                        );
                        value = evaluate_contract_expression_with_environment(
                            &fold_values,
                            array_refs,
                            pre_state,
                            post_state,
                            result,
                            assumptions,
                            body,
                            predicate_environment,
                            click_function_environment,
                            active_functions,
                        )?;
                    }
                    Ok(value)
                }
                _ => {
                    let mut fold_values = parameter_values.clone();
                    fold_values.insert(
                        accumulator.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                            accumulator,
                            0,
                        ))),
                    );
                    fold_values.insert(
                        item.clone(),
                        CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                    );
                    let body_value = evaluate_contract_expression_with_environment(
                        &fold_values,
                        array_refs,
                        pre_state,
                        post_state,
                        result,
                        assumptions,
                        body,
                        predicate_environment,
                        click_function_environment,
                        active_functions,
                    )?;
                    symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                }
            }
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                value,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let value = checked_contract_let_value(value, *c_type, name)?;
            let mut let_values = parameter_values.clone();
            let_values.insert(name.clone(), value);
            evaluate_contract_expression_with_environment(
                &let_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                body,
                predicate_environment,
                click_function_environment,
                active_functions,
            )
        }
        ContractExpression::Call { name, arguments } => evaluate_click_function_call(
            click_function_environment,
            name,
            arguments,
            parameter_values,
            array_refs,
            pre_state,
            post_state,
            result,
            assumptions,
            predicate_environment,
            active_functions,
        ),
    }
}

fn array_refs_with_memory(array_refs: &ClickArrayRefs, memory: &CMemory) -> ClickArrayRefs {
    array_refs
        .iter()
        .map(|(name, array_ref)| {
            (
                name.clone(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: array_ref.pointer.clone(),
                    element_type: array_ref.element_type,
                },
            )
        })
        .collect()
}

fn visit_selector_is_function_entry(selector: &VisitSelector) -> bool {
    matches!(
        selector,
        VisitSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        })
    )
}

fn evaluate_click_function_call(
    click_function_environment: &ClickFunctionEnvironment,
    name: &str,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<CValue, String> {
    let definition = click_function_environment
        .get(name)
        .ok_or_else(|| format!("unknown function `{name}`"))?;
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "function `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    if !active_functions.insert(name.to_string()) {
        return Err(format!(
            "recursive function call `{name}` is not supported yet"
        ));
    }

    let mut function_values = BTreeMap::new();
    let mut function_array_refs = BTreeMap::new();
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        let value = if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "function `{}` parameter `{}` is not an array-ref parameter",
                        definition.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "function `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    definition.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            let pointer = array_ref.pointer.clone();
            function_array_refs.insert(parameter.name().to_string(), array_ref);
            CValue::Pointer(pointer)
        } else {
            evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?
        };
        function_values.insert(parameter.name().to_string(), value);
    }

    let value = evaluate_contract_expression_with_environment(
        &function_values,
        &function_array_refs,
        post_state,
        post_state,
        None,
        assumptions,
        definition.body(),
        predicate_environment,
        click_function_environment,
        active_functions,
    )?;
    active_functions.remove(name);

    if !c_value_matches_click_type(&value, definition.return_type()) {
        return Err(format!(
            "function `{}` returned {value:?}, which does not match {:?}",
            definition.name(),
            definition.return_type()
        ));
    }
    Ok(value)
}

fn evaluate_contract_array_ref_with_environment(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<ClickArrayRef, String> {
    match expression {
        ContractExpression::Old(expression) => {
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                pre_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `old(...)` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            let element_type =
                contract_array_ref_element_type(array_refs, expression).unwrap_or(CType::Int32);
            Ok(ClickArrayRef {
                memory: pre_state.memory().clone(),
                pointer,
                element_type,
            })
        }
        ContractExpression::At {
            selector,
            expression,
        } if visit_selector_is_function_entry(selector) => {
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                pre_state,
                None,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference expression inside `at(function.entry, ...)` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            let element_type =
                contract_array_ref_element_type(array_refs, expression).unwrap_or(CType::Int32);
            Ok(ClickArrayRef {
                memory: pre_state.memory().clone(),
                pointer,
                element_type,
            })
        }
        ContractExpression::At { .. } => Err(
            "`at(...)` is currently supported in concrete array references only for `function.entry`"
                .to_string(),
        ),
        ContractExpression::CFragment(CExpression::Variable(name)) => {
            if let Some(array_ref) = array_refs.get(name) {
                return Ok(array_ref.clone());
            }
            let pointer_value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let CValue::Pointer(pointer) = pointer_value else {
                return Err(format!(
                    "array reference `{name}` did not evaluate to a pointer: `{pointer_value:?}`"
                ));
            };
            Ok(ClickArrayRef {
                memory: post_state.memory().clone(),
                pointer,
                element_type: CType::Int32,
            })
        }
        ContractExpression::Add(left, right) => {
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    right,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        offset,
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                right,
                predicate_environment,
                click_function_environment,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    left,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        offset,
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            evaluate_pointer_expression_as_current_array_ref(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )
        }
        ContractExpression::Subtract(left, right) => {
            if let Ok(array_ref) = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                left,
                predicate_environment,
                click_function_environment,
                active_functions,
            ) {
                let offset = evaluate_contract_expression_with_environment(
                    parameter_values,
                    array_refs,
                    pre_state,
                    post_state,
                    result,
                    assumptions,
                    right,
                    predicate_environment,
                    click_function_environment,
                    active_functions,
                )?;
                let CValue::Int32(offset) = offset else {
                    return Err(format!(
                        "array reference offset did not evaluate to int32: `{offset:?}`"
                    ));
                };
                let element_type = array_ref.element_type;
                return Ok(ClickArrayRef {
                    memory: array_ref.memory,
                    pointer: offset_pointer_by_elements(
                        array_ref.pointer,
                        bitvector32_subtract(Bitvector32Term::Constant(0), offset),
                        element_type.byte_width(),
                    ),
                    element_type,
                });
            }
            evaluate_pointer_expression_as_current_array_ref(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                expression,
                predicate_environment,
                click_function_environment,
                active_functions,
            )
        }
        _ => evaluate_pointer_expression_as_current_array_ref(
            parameter_values,
            array_refs,
            pre_state,
            post_state,
            result,
            assumptions,
            expression,
            predicate_environment,
            click_function_environment,
            active_functions,
        ),
    }
}

fn contract_array_ref_element_type(
    array_refs: &ClickArrayRefs,
    expression: &ContractExpression,
) -> Option<CType> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name)) => {
            array_refs.get(name).map(|array_ref| array_ref.element_type)
        }
        ContractExpression::Old(expression) => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::At { expression, .. } => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::Add(left, right) => contract_array_ref_element_type(array_refs, left)
            .or_else(|| contract_array_ref_element_type(array_refs, right)),
        ContractExpression::Subtract(left, _) => contract_array_ref_element_type(array_refs, left),
        _ => None,
    }
}

fn evaluate_pointer_expression_as_current_array_ref(
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &ContractExpression,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<ClickArrayRef, String> {
    let pointer_value = evaluate_contract_expression_with_environment(
        parameter_values,
        array_refs,
        pre_state,
        post_state,
        result,
        assumptions,
        expression,
        predicate_environment,
        click_function_environment,
        active_functions,
    )?;
    let CValue::Pointer(pointer) = pointer_value else {
        return Err(format!(
            "array reference expression did not evaluate to a pointer: `{pointer_value:?}`"
        ));
    };
    Ok(ClickArrayRef {
        memory: post_state.memory().clone(),
        pointer,
        element_type: CType::Int32,
    })
}

fn lower_predicate_call_arguments_with_environment(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    active_functions: &mut BTreeSet<String>,
) -> Result<Vec<Term>, String> {
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "predicate `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }

    let mut lowered_arguments = Vec::new();
    for (parameter, argument) in definition.parameters().iter().zip(arguments) {
        if parameter_is_click_array_ref(parameter) {
            let array_ref = evaluate_contract_array_ref_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            let expected_element_type =
                click_array_element_type(parameter.c_type()).ok_or_else(|| {
                    format!(
                        "predicate `{}` parameter `{}` is not an array-ref parameter",
                        definition.name(),
                        parameter.name()
                    )
                })?;
            if array_ref.element_type != expected_element_type {
                return Err(format!(
                    "predicate `{}` parameter `{}` expects {:?} array elements, got {:?}",
                    definition.name(),
                    parameter.name(),
                    expected_element_type,
                    array_ref.element_type
                ));
            }
            lowered_arguments.push(Term::CMemory(array_ref.memory));
            lowered_arguments.push(Term::CValue(CValue::Pointer(array_ref.pointer)));
        } else {
            let value = evaluate_contract_expression_with_environment(
                parameter_values,
                array_refs,
                pre_state,
                post_state,
                result,
                assumptions,
                argument,
                predicate_environment,
                click_function_environment,
                active_functions,
            )?;
            lowered_arguments.push(Term::CValue(value));
        }
    }
    Ok(lowered_arguments)
}

fn c_value_matches_click_type(value: &CValue, c_type: C0Type) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), C0Type::Int32)
            | (CValue::UInt8(_), C0Type::UInt8)
            | (CValue::Pointer(_), C0Type::Int32Pointer)
            | (CValue::Pointer(_), C0Type::UInt8Pointer)
    )
}

fn checked_contract_let_value(
    value: CValue,
    c_type: Option<C0Type>,
    name: &str,
) -> Result<CValue, String> {
    let Some(c_type) = c_type else {
        return Ok(value);
    };
    if c_value_matches_click_type(&value, c_type) {
        Ok(value)
    } else {
        Err(format!(
            "let binding `{name}` evaluated to {value:?}, which does not match {c_type:?}"
        ))
    }
}

fn evaluate_c_contract_expression(
    parameter_values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &CExpression,
) -> Result<CValue, String> {
    match expression {
        CExpression::Value(value) => Ok(value.clone()),
        CExpression::Variable(name) if name == "result" => result
            .cloned()
            .ok_or_else(|| "`result` is not available inside `old(...)`".to_string()),
        CExpression::Variable(name) => parameter_values
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown contract variable `{name}`")),
        CExpression::Add(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_add(left, right)
        }
        CExpression::Subtract(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        CExpression::Multiply(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        CExpression::Divide(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        CExpression::Remainder(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        CExpression::ShiftLeft(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        CExpression::ShiftRight(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        CExpression::BitwiseAnd(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        CExpression::BitwiseOr(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        CExpression::BitwiseXor(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        CExpression::BitwiseNot(expression) => {
            let value = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                expression,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        CExpression::Load(pointer) => {
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            evaluate_contract_memory_load(state, pointer, CType::Int32, assumptions)
        }
        CExpression::Index(base, index) => {
            let base =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, base)?;
            let index = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            evaluate_contract_memory_load(state, pointer, CType::Int32, assumptions)
        }
        _ => Err(format!(
            "unsupported postcondition expression `{expression:?}`"
        )),
    }
}

fn evaluate_contract_memory_load(
    state: &CState,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    evaluate_contract_memory_load_from_memory(state.memory(), pointer, value_type, assumptions)
}

fn evaluate_contract_memory_load_from_memory(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    match memory.load(&pointer) {
        crate::kernel::CExpressionOutcome::Value(value)
            if c_value_matches_kernel_type(&value, value_type) =>
        {
            Ok(value)
        }
        crate::kernel::CExpressionOutcome::Value(value) => Err(format!(
            "load from {pointer:?} produced {value:?}, not {value_type:?}"
        )),
        _ if assumptions.proves(&Proposition::CMemoryCanLoad {
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: value_type.byte_width(),
        }) =>
        {
            symbolic_contract_memory_load(memory, pointer, value_type)
        }
        outcome => Err(format!("load from {pointer:?} produced {outcome:?}")),
    }
}

fn c_value_matches_kernel_type(value: &CValue, c_type: CType) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), CType::Int32) | (CValue::UInt8(_), CType::UInt8)
    )
}

fn symbolic_contract_memory_load(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
) -> Result<CValue, String> {
    let load = Bitvector32Term::MemoryLoad(Box::new(memory.clone()), Box::new(pointer));
    match value_type {
        CType::Int32 => Ok(CValue::Int32(load)),
        CType::UInt8 => Ok(CValue::UInt8(load)),
        CType::Int32Pointer | CType::UInt8Pointer | CType::Int32Array(_) | CType::UInt8Array(_) => {
            Err(format!("cannot symbolically load {value_type:?}"))
        }
    }
}

fn evaluate_postcondition_add(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_add(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add pointer and `{offset:?}`")),
        (offset, CValue::Pointer(pointer)) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add `{offset:?}` and pointer")),
        (left, right) => Err(format!("cannot add `{left:?}` and `{right:?}`")),
    }
}

fn evaluate_postcondition_sub(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_subtract(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => {
            let Some(index) = promoted_int32_term(&offset) else {
                return Err(format!("cannot subtract `{offset:?}` from pointer"));
            };
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(format!("cannot subtract `{right:?}` from `{left:?}`")),
    }
}

fn evaluate_postcondition_multiply(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(bitvector32_multiply(left_term, right_term)))
    } else {
        Err(format!("cannot multiply `{left:?}` and `{right:?}`"))
    }
}

fn evaluate_postcondition_divide(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_divide(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot divide `{left:?}` by `{right:?}`"))
    }
}

fn evaluate_postcondition_remainder(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_remainder(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot compute `{left:?}` % `{right:?}`"))
    }
}

fn evaluate_postcondition_shift_left(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_left(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `<<` to `{left:?}` and `{right:?}`"))
    }
}

fn evaluate_postcondition_shift_right(left: CValue, right: CValue) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_right(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `>>` to `{left:?}` and `{right:?}`"))
    }
}

fn evaluate_postcondition_bitwise_binary(
    left: CValue,
    right: CValue,
    operator: &str,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(apply(left_term, right_term)))
    } else {
        Err(format!(
            "cannot apply `{operator}` to `{left:?}` and `{right:?}`"
        ))
    }
}

fn evaluate_postcondition_bitwise_not(value: CValue) -> Result<CValue, String> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(format!("cannot apply `~` to `{value:?}`"))
    }
}

fn evaluate_postcondition_pointer_add(left: CValue, right: CValue) -> Result<Pointer, String> {
    match evaluate_postcondition_add(left, right)? {
        CValue::Pointer(pointer) => Ok(pointer),
        value => Err(format!(
            "index base did not evaluate to a pointer: `{value:?}`"
        )),
    }
}

fn offset_pointer_by_int32_elements(pointer: Pointer, elements: Bitvector32Term) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
    element_width: u32,
) -> Pointer {
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(
            pointer.offset,
            scale_int32_offset(elements, i64::from(element_width)),
        ),
    }
}

fn add_pointer_offset(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

fn scale_int32_offset(value: Bitvector32Term, byte_width: i64) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}

fn standard_library_definitions() -> Result<
    (
        Vec<PredicateDefinition>,
        Vec<ClickFunctionDefinition>,
        Vec<ResourceDefinition>,
        Vec<TheoremDefinition>,
    ),
    ClickError,
> {
    let file = expand_declared_resource_clauses(parser::parse_file_items(CLICK_STANDARD_LIBRARY)?)?;
    if !file.verifying_sources().is_empty() || !file.function_blocks().is_empty() {
        return Err(ClickError::new(
            "internal Click standard library must not contain verifying sources or C function specs",
        ));
    }
    Ok((
        file.predicate_definitions().to_vec(),
        file.click_function_definitions().to_vec(),
        file.resource_definitions().to_vec(),
        file.theorem_definitions().to_vec(),
    ))
}

fn expand_declared_resource_clauses(mut file: ClickFile) -> Result<ClickFile, ClickError> {
    let resource_parameters = file
        .resource_definitions()
        .iter()
        .map(|definition| {
            (
                definition.name().to_string(),
                definition
                    .parameters()
                    .iter()
                    .map(FunctionParameter::c_type)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    file.resource_definitions = file
        .resource_definitions
        .drain(..)
        .map(|definition| expand_declared_resource_definition(definition, &resource_parameters))
        .collect::<Result<Vec<_>, _>>()?;

    for function in &mut file.function_blocks {
        function.requires = function
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_parameters)
            })
            .collect::<Result<Vec<_>, _>>()?;
        function.ensures = function
            .ensures
            .drain(..)
            .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
        function.effects = function
            .effects
            .drain(..)
            .map(|clause| expand_declared_resource_effect_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
        function.structural_clauses = function
            .structural_clauses
            .drain(..)
            .map(|clause| expand_declared_resource_structural_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
    }

    for theorem in &mut file.theorem_definitions {
        theorem.requires = theorem
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_parameters)
            })
            .collect::<Result<Vec<_>, _>>()?;
        theorem.ensures = theorem
            .ensures
            .drain(..)
            .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
    }

    Ok(file)
}

fn expand_declared_resource_definition(
    mut definition: ResourceDefinition,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ResourceDefinition, ClickError> {
    if let Some(representation) = definition.representation {
        definition.representation = Some(expand_declared_resource_representation(
            representation,
            resource_parameters,
        )?);
    }
    Ok(definition)
}

fn expand_declared_resource_representation(
    representation: ResourceRepresentation,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ResourceRepresentation, ClickError> {
    Ok(ResourceRepresentation {
        contains: representation
            .contains
            .into_iter()
            .map(|resource| expand_declared_resource_clause(resource, resource_parameters))
            .collect::<Result<Vec<_>, _>>()?,
        invariants: representation.invariants,
    })
}

fn expand_declared_resource_requirement(
    requirement: Requirement,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<Requirement, ClickError> {
    match requirement {
        Requirement::Labeled { label, requirement } => Ok(Requirement::Labeled {
            label,
            requirement: Box::new(expand_declared_resource_requirement(
                *requirement,
                resource_parameters,
            )?),
        }),
        Requirement::Proposition(ClickProposition::PredicateCall { name, arguments })
            if resource_parameters.contains_key(&name) =>
        {
            let parameter_types =
                declared_resource_parameter_types(&name, arguments.len(), resource_parameters)?;
            Ok(Requirement::Resource(ResourceClause::Named {
                name,
                arguments,
                parameter_types,
            }))
        }
        _ => Ok(requirement),
    }
}

fn expand_declared_resource_ensure_clause(
    mut clause: EnsureClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<EnsureClause, ClickError> {
    if let Ensure::Proposition(ClickProposition::PredicateCall { name, arguments }) = clause.ensure
    {
        if resource_parameters.contains_key(&name) {
            let parameter_types =
                declared_resource_parameter_types(&name, arguments.len(), resource_parameters)?;
            clause.ensure = Ensure::Resource(ResourceClause::Named {
                name,
                arguments,
                parameter_types,
            });
        } else {
            clause.ensure =
                Ensure::Proposition(ClickProposition::PredicateCall { name, arguments });
        }
    }
    clause.proof = expand_declared_resource_proof(clause.proof, resource_parameters)?;
    Ok(clause)
}

fn expand_declared_resource_effect_clause(
    mut clause: EffectClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<EffectClause, ClickError> {
    clause.proof = expand_declared_resource_proof(clause.proof, resource_parameters)?;
    Ok(clause)
}

fn expand_declared_resource_structural_clause(
    mut clause: StructuralClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<StructuralClause, ClickError> {
    clause.items = clause
        .items
        .into_iter()
        .map(|item| expand_declared_resource_structural_item(item, resource_parameters))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(clause)
}

fn expand_declared_resource_structural_item(
    mut item: StructuralItem,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<StructuralItem, ClickError> {
    item.proof = expand_declared_resource_proof(item.proof, resource_parameters)?;
    Ok(item)
}

fn expand_declared_resource_proof(
    proof: Proof,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<Proof, ClickError> {
    match proof {
        Proof::Tactic(_) => Ok(proof),
        Proof::Steps(steps) => Ok(Proof::Steps(
            steps
                .into_iter()
                .map(|step| expand_declared_resource_proof_step(step, resource_parameters))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

fn expand_declared_resource_proof_step(
    step: ProofStep,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ProofStep, ClickError> {
    match step {
        ProofStep::OpenResource(resource) => Ok(ProofStep::OpenResource(
            expand_declared_resource_clause(resource, resource_parameters)?,
        )),
        ProofStep::CloseResource(resource) => Ok(ProofStep::CloseResource(
            expand_declared_resource_clause(resource, resource_parameters)?,
        )),
        _ => Ok(step),
    }
}

fn expand_declared_resource_clause(
    resource: ResourceClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ResourceClause, ClickError> {
    match resource {
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } if parameter_types.is_empty() => {
            let parameter_types =
                declared_resource_parameter_types(&name, arguments.len(), resource_parameters)?;
            Ok(ResourceClause::Named {
                name,
                arguments,
                parameter_types,
            })
        }
        resource => Ok(resource),
    }
}

fn declared_resource_parameter_types(
    name: &str,
    actual: usize,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<Vec<C0Type>, ClickError> {
    let Some(parameters) = resource_parameters.get(name) else {
        return Err(ClickError::new(format!("unknown resource `{name}`")));
    };
    let expected = parameters.len();
    if expected != actual {
        return Err(ClickError::new(format!(
            "resource `{name}` expects {expected} argument(s), got {actual}"
        )));
    }
    Ok(parameters.clone())
}

fn combined_predicate_definitions(
    file: &ClickFile,
) -> Result<Vec<PredicateDefinition>, ClickError> {
    let (mut definitions, _, _, _) = standard_library_definitions()?;
    definitions.extend(file.predicate_definitions().iter().cloned());
    Ok(definitions)
}

fn combined_click_function_definitions(
    file: &ClickFile,
) -> Result<Vec<ClickFunctionDefinition>, ClickError> {
    let (_, mut definitions, _, _) = standard_library_definitions()?;
    definitions.extend(file.click_function_definitions().iter().cloned());
    Ok(definitions)
}

fn combined_resource_definitions(file: &ClickFile) -> Result<Vec<ResourceDefinition>, ClickError> {
    let (_, _, mut definitions, _) = standard_library_definitions()?;
    definitions.extend(file.resource_definitions().iter().cloned());
    Ok(definitions)
}

fn combined_theorem_definitions(file: &ClickFile) -> Result<Vec<TheoremDefinition>, ClickError> {
    let (_, _, _, mut definitions) = standard_library_definitions()?;
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok(definitions)
}

fn combined_theorem_definitions_with_stdlib_ensure_count(
    file: &ClickFile,
) -> Result<(Vec<TheoremDefinition>, usize), ClickError> {
    let (_, _, _, mut definitions) = standard_library_definitions()?;
    let stdlib_ensure_count = definitions
        .iter()
        .map(|definition| definition.ensures().len())
        .sum();
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok((definitions, stdlib_ensure_count))
}

fn validate_click_definitions(file: &ClickFile) -> Result<(), ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let resource_definitions = combined_resource_definitions(file)?;
    let theorem_definitions = combined_theorem_definitions(file)?;

    let mut predicates = BTreeMap::new();
    for definition in &predicate_definitions {
        if predicates
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate predicate definition `{}`",
                definition.name()
            )));
        }
    }

    let mut click_functions = BTreeMap::new();
    let mut click_function_types = BTreeMap::new();
    for definition in &click_function_definitions {
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a function",
                definition.name()
            )));
        }
        if click_functions
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate function definition `{}`",
                definition.name()
            )));
        }
        click_function_types.insert(
            definition.name().to_string(),
            ClickFunctionType {
                parameters: definition.parameters().to_vec(),
                return_type: definition.return_type(),
            },
        );
    }

    let mut resources = BTreeMap::new();
    for definition in &resource_definitions {
        if matches!(definition.name(), "read" | "write" | "free") {
            return Err(ClickError::new(format!(
                "`{}` is a built-in resource name",
                definition.name()
            )));
        }
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a resource",
                definition.name()
            )));
        }
        if click_functions.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a function and a resource",
                definition.name()
            )));
        }
        if resources
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate resource definition `{}`",
                definition.name()
            )));
        }
    }

    let mut theorems = BTreeMap::new();
    for definition in &theorem_definitions {
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a theorem",
                definition.name()
            )));
        }
        if click_functions.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a function and a theorem",
                definition.name()
            )));
        }
        if resources.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a resource and a theorem",
                definition.name()
            )));
        }
        if theorems
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate theorem definition `{}`",
                definition.name()
            )));
        }
    }

    let predicate_definition_map = predicate_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let click_function_definition_map = click_function_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);

    for definition in &resource_definitions {
        validate_resource_definition(
            definition,
            &resources,
            &predicates,
            &click_functions,
            &click_function_types,
            &predicate_definition_map,
            &click_function_definition_map,
            &predicate_environment,
            &click_function_environment,
        )?;
    }
    reject_resource_representation_cycles(&resource_definitions)?;

    for definition in &predicate_definitions {
        validate_predicate_calls_in_proposition(
            definition.body(),
            &predicates,
            &click_functions,
            &format!("predicate `{}`", definition.name()),
        )?;
    }

    let mut function_calls = BTreeMap::new();
    for definition in &click_function_definitions {
        validate_click_function_expression(
            definition.body(),
            &click_functions,
            &format!("function `{}`", definition.name()),
        )?;
        let mut calls = BTreeSet::new();
        collect_click_function_calls(definition.body(), &mut calls);
        function_calls.insert(definition.name().to_string(), calls);
    }
    reject_recursive_click_functions(&function_calls)?;

    for theorem in &theorem_definitions {
        validate_theorem_definition(
            theorem,
            &predicates,
            &click_functions,
            &click_function_types,
        )?;
    }

    let user_click_functions = file
        .click_function_definitions()
        .iter()
        .map(|definition| definition.name())
        .collect::<BTreeSet<_>>();

    for function in file.function_blocks() {
        if user_click_functions.contains(function.signature().name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a Click function and a C function spec",
                function.signature().name()
            )));
        }
        if theorems.contains_key(function.signature().name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a theorem and a C function spec",
                function.signature().name()
            )));
        }
        if function.ensures().is_empty()
            && function.effects().is_empty()
            && !function
                .requires()
                .iter()
                .any(requirement_contains_resource)
        {
            return Err(ClickError::new(format!(
                "`{}` must contain at least one `ensures`, `immutable`, `mutable`, `mutable_field`, or resource-consuming `requires` clause",
                function.signature().name()
            )));
        }
        let requires_type_environment =
            function_signature_type_environment(function.signature(), false);
        let ensures_type_environment =
            function_signature_type_environment(function.signature(), true);

        reject_duplicate_named_resource_clauses(
            function
                .requires()
                .iter()
                .filter_map(|requirement| match requirement.inner() {
                    Requirement::Resource(resource) => Some(resource),
                    _ => None,
                }),
            &format!("requires clauses in `{}`", function.signature().name()),
        )?;
        reject_duplicate_named_resource_clauses(
            function
                .ensures()
                .iter()
                .filter_map(|ensure| match ensure.ensure() {
                    Ensure::Resource(resource) => Some(resource),
                    _ => None,
                }),
            &format!("ensures clauses in `{}`", function.signature().name()),
        )?;

        let mut requirement_labels = BTreeSet::new();
        for requirement in function.requires() {
            if let Some(label) = requirement.label() {
                if !requirement_labels.insert(label.to_string()) {
                    return Err(ClickError::new(format!(
                        "duplicate requirement label `{label}` in `{}`",
                        function.signature().name()
                    )));
                }
            }
            if let Some(proposition) = requirement.proposition() {
                validate_predicate_calls_in_proposition(
                    proposition,
                    &predicates,
                    &click_functions,
                    &format!("requires clause in `{}`", function.signature().name()),
                )?;
            } else if let Requirement::Resource(resource) = requirement.inner() {
                validate_resource_clause(
                    resource,
                    &resources,
                    &click_functions,
                    &click_function_types,
                    &requires_type_environment,
                    &format!("requires clause in `{}`", function.signature().name()),
                )?;
            }
        }

        for structural_clause in function.structural_clauses() {
            for item in structural_clause.items() {
                if let Some(proposition) = item.proposition() {
                    validate_predicate_calls_in_proposition(
                        proposition,
                        &predicates,
                        &click_functions,
                        &format!(
                            "{:?} clause in `{}`",
                            item.kind(),
                            function.signature().name()
                        ),
                    )?;
                }
            }
        }

        for ensure in function.ensures() {
            match ensure.ensure() {
                Ensure::Proposition(proposition) => validate_predicate_calls_in_proposition(
                    proposition,
                    &predicates,
                    &click_functions,
                    &format!("ensures clause in `{}`", function.signature().name()),
                )?,
                Ensure::Resource(resource) => validate_resource_clause(
                    resource,
                    &resources,
                    &click_functions,
                    &click_function_types,
                    &ensures_type_environment,
                    &format!("ensures clause in `{}`", function.signature().name()),
                )?,
            }
        }
    }

    Ok(())
}

fn validate_theorem_definition(
    theorem: &TheoremDefinition,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
) -> Result<(), ClickError> {
    if theorem.ensures().is_empty() {
        return Err(ClickError::new(format!(
            "theorem `{}` must contain at least one `ensures` clause",
            theorem.name()
        )));
    }

    let variables = theorem_type_environment(theorem);
    let mut requirement_labels = BTreeSet::new();
    for requirement in theorem.requires() {
        if let Some(label) = requirement.label() {
            if !requirement_labels.insert(label.to_string()) {
                return Err(ClickError::new(format!(
                    "duplicate requirement label `{label}` in theorem `{}`",
                    theorem.name()
                )));
            }
        }
        let Some(proposition) = requirement.proposition() else {
            return Err(ClickError::new(format!(
                "pure theorem `{}` currently supports proposition `requires` clauses only",
                theorem.name()
            )));
        };
        validate_predicate_calls_in_proposition(
            proposition,
            predicates,
            click_functions,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
        validate_proposition_expression_types(
            proposition,
            &variables,
            click_function_types,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
    }

    for ensure in theorem.ensures() {
        let Ensure::Proposition(proposition) = ensure.ensure() else {
            return Err(ClickError::new(format!(
                "pure theorem `{}` currently supports proposition `ensures` clauses only",
                theorem.name()
            )));
        };
        validate_predicate_calls_in_proposition(
            proposition,
            predicates,
            click_functions,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_proposition_expression_types(
            proposition,
            &variables,
            click_function_types,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_pure_theorem_proof(theorem.name(), ensure.proof())?;
    }

    Ok(())
}

fn validate_resource_definition(
    definition: &ResourceDefinition,
    resources: &BTreeMap<String, usize>,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    let Some(representation) = definition.representation() else {
        return Ok(());
    };
    let variables = definition
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    reject_duplicate_named_resource_clauses(
        representation.contains(),
        &format!("resource `{}` representation", definition.name()),
    )?;
    for resource in representation.contains() {
        validate_resource_clause(
            resource,
            resources,
            click_functions,
            click_function_types,
            &variables,
            &format!("resource `{}` representation", definition.name()),
        )?;
    }
    for invariant in representation.invariants() {
        if proposition_contains_old_expression(invariant) {
            return Err(ClickError::new(format!(
                "`old(...)` is not available inside resource `{}` invariant",
                definition.name()
            )));
        }
        if proposition_contains_at_expression(invariant) {
            return Err(ClickError::new(format!(
                "`at(...)` is not available inside resource `{}` invariant",
                definition.name()
            )));
        }
        validate_predicate_calls_in_proposition(
            invariant,
            predicates,
            click_functions,
            &format!("resource `{}` invariant", definition.name()),
        )?;
        validate_proposition_expression_types(
            invariant,
            &variables,
            click_function_types,
            &format!("resource `{}` invariant", definition.name()),
        )?;
        validate_resource_invariant_memory_ownership(
            definition,
            representation,
            invariant,
            predicate_definitions,
            click_function_definitions,
            predicate_environment,
            click_function_environment,
        )?;
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceInvariantRead {
    base: CExpression,
    index: CExpression,
    expression: String,
}

fn validate_resource_invariant_memory_ownership(
    definition: &ResourceDefinition,
    representation: &ResourceRepresentation,
    invariant: &ClickProposition,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    let mut reads = Vec::new();
    let mut visited_predicates = Vec::new();
    let mut visited_functions = Vec::new();
    collect_resource_invariant_reads_from_proposition(
        invariant,
        predicate_definitions,
        click_function_definitions,
        &mut visited_predicates,
        &mut visited_functions,
        &mut reads,
        definition.name(),
    )?;
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(definition.parameters());
    let array_refs = pure_theorem_array_refs(definition.parameters(), &values, &memory);
    let mut scalar_assumptions = Vec::new();
    collect_resource_invariant_scalar_assumptions_from_proposition(
        invariant,
        predicate_definitions,
        &values,
        &array_refs,
        &memory,
        predicate_environment,
        click_function_environment,
        &mut Vec::new(),
        &mut scalar_assumptions,
        definition.name(),
    )?;
    let assumptions = assumptions_from_propositions(&scalar_assumptions);
    for read in reads {
        if !resource_invariant_read_is_owned(
            &read,
            representation.contains(),
            &assumptions,
            &values,
            &array_refs,
            &memory,
            predicate_environment,
            click_function_environment,
        ) {
            return Err(ClickError::new(format!(
                "resource `{}` invariant reads `{}` without a covering contained `write(...)` resource",
                definition.name(),
                read.expression
            )));
        }
    }
    Ok(())
}

fn collect_resource_invariant_scalar_assumptions_from_proposition(
    proposition: &ClickProposition,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    visited_predicates: &mut Vec<String>,
    assumptions: &mut Vec<Proposition>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { .. } => {
            let mut lowerer = KernelPropositionLowerer::new(
                values.clone(),
                array_refs.clone(),
                memory.clone(),
                predicate_environment,
                click_function_environment,
            );
            if let Ok(proposition) = lowerer.lower_requirement_proposition(proposition) {
                assumptions.push(proposition);
            }
            Ok(())
        }
        ClickProposition::And(left, right) => {
            collect_resource_invariant_scalar_assumptions_from_proposition(
                left,
                predicate_definitions,
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
                visited_predicates,
                assumptions,
                resource_name,
            )?;
            collect_resource_invariant_scalar_assumptions_from_proposition(
                right,
                predicate_definitions,
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
                visited_predicates,
                assumptions,
                resource_name,
            )
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let Some(definition) = predicate_definitions.get(name.as_str()) else {
                return Ok(());
            };
            if visited_predicates.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` invariant cannot use recursive predicate `{name}`"
                )));
            }
            visited_predicates.push(name.clone());
            let body = instantiate_click_predicate_definition(definition, arguments).map_err(
                |message| {
                    ClickError::new(format!(
                        "resource `{resource_name}` invariant could not inspect predicate `{name}`: {message}"
                    ))
                },
            )?;
            let result = collect_resource_invariant_scalar_assumptions_from_proposition(
                &body,
                predicate_definitions,
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
                visited_predicates,
                assumptions,
                resource_name,
            );
            visited_predicates.pop();
            result
        }
        ClickProposition::Or(_, _)
        | ClickProposition::Not(_)
        | ClickProposition::Implies(_, _)
        | ClickProposition::ForAll { .. }
        | ClickProposition::Exists { .. }
        | ClickProposition::RangeAll { .. }
        | ClickProposition::RangeAny { .. } => Ok(()),
    }
}

fn collect_resource_invariant_reads_from_proposition(
    proposition: &ClickProposition,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut Vec<String>,
    reads: &mut Vec<ResourceInvariantRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_resource_invariant_reads_from_contract_expression(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_resource_invariant_reads_from_proposition(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_proposition(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            collect_resource_invariant_reads_from_proposition(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_resource_invariant_reads_from_contract_expression(
                start,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                end,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_proposition(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::PredicateCall { name, arguments } => {
            for argument in arguments {
                collect_resource_invariant_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            let Some(definition) = predicate_definitions.get(name.as_str()) else {
                return Ok(());
            };
            if visited_predicates.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` invariant cannot use recursive predicate `{name}`"
                )));
            }
            visited_predicates.push(name.clone());
            let body = instantiate_click_predicate_definition(definition, arguments).map_err(
                |message| {
                    ClickError::new(format!(
                        "resource `{resource_name}` invariant could not inspect predicate `{name}`: {message}"
                    ))
                },
            )?;
            let result = collect_resource_invariant_reads_from_proposition(
                &body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            );
            visited_predicates.pop();
            result
        }
    }
}

fn collect_resource_invariant_reads_from_contract_expression(
    expression: &ContractExpression,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut Vec<String>,
    reads: &mut Vec<ResourceInvariantRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match expression {
        ContractExpression::CFragment(expression) => {
            collect_resource_invariant_reads_from_c_expression(expression, reads);
            Ok(())
        }
        ContractExpression::Old(_) => Err(ClickError::new(format!(
            "`old(...)` is not available inside resource `{resource_name}` invariant"
        ))),
        ContractExpression::At { .. } => Err(ClickError::new(format!(
            "`at(...)` is not available inside resource `{resource_name}` invariant"
        ))),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            collect_resource_invariant_reads_from_contract_expression(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::BitwiseNot(expression) => {
            collect_resource_invariant_reads_from_contract_expression(
                expression,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Index(base, index) => {
            collect_resource_invariant_reads_from_contract_expression(
                base,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                index,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            let Some(base) = contract_expression_as_c_fragment(base) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` invariant reads `{}` in a form that cannot be matched to a contained `write(...)` resource",
                    describe_contract_expression(expression)
                )));
            };
            let Some(index) = contract_expression_as_c_fragment(index) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` invariant reads `{}` in a form that cannot be matched to a contained `write(...)` resource",
                    describe_contract_expression(expression)
                )));
            };
            reads.push(ResourceInvariantRead {
                expression: describe_contract_expression(expression),
                base,
                index,
            });
            Ok(())
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_resource_invariant_reads_from_proposition(
                condition,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                then_branch,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                else_branch,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_resource_invariant_reads_from_contract_expression(
                start,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                end,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                initial,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Let { value, body, .. } => {
            collect_resource_invariant_reads_from_contract_expression(
                value,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_invariant_reads_from_contract_expression(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Call { name, arguments } => {
            for argument in arguments {
                collect_resource_invariant_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            let Some(definition) = click_function_definitions.get(name.as_str()) else {
                return Ok(());
            };
            if visited_functions.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` invariant cannot use recursive function `{name}`"
                )));
            }
            visited_functions.push(name.clone());
            let substitutions = definition
                .parameters()
                .iter()
                .zip(arguments)
                .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                .collect::<BTreeMap<_, _>>();
            let body = substitute_contract_expression(definition.body(), &substitutions).map_err(
                |message| {
                    ClickError::new(format!(
                        "resource `{resource_name}` invariant could not inspect function `{name}`: {message}"
                    ))
                },
            )?;
            let result = collect_resource_invariant_reads_from_contract_expression(
                &body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            );
            visited_functions.pop();
            result
        }
    }
}

fn collect_resource_invariant_reads_from_c_expression(
    expression: &CExpression,
    reads: &mut Vec<ResourceInvariantRead>,
) {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) => {}
        CExpression::AddressOf(_) => {}
        CExpression::Load(pointer) => {
            collect_resource_invariant_reads_from_c_expression(pointer, reads);
            reads.push(ResourceInvariantRead {
                base: pointer.as_ref().clone(),
                index: CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                expression: describe_c_expression(expression),
            });
        }
        CExpression::Index(base, index) => {
            collect_resource_invariant_reads_from_c_expression(base, reads);
            collect_resource_invariant_reads_from_c_expression(index, reads);
            reads.push(ResourceInvariantRead {
                base: base.as_ref().clone(),
                index: index.as_ref().clone(),
                expression: describe_c_expression(expression),
            });
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
        | CExpression::BitwiseXor(left, right) => {
            collect_resource_invariant_reads_from_c_expression(left, reads);
            collect_resource_invariant_reads_from_c_expression(right, reads);
        }
        CExpression::Not(expression) | CExpression::BitwiseNot(expression) => {
            collect_resource_invariant_reads_from_c_expression(expression, reads);
        }
    }
}

fn resource_invariant_read_is_owned(
    read: &ResourceInvariantRead,
    contained: &[ResourceClause],
    assumptions: &Assumptions,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> bool {
    contained.iter().any(|resource| {
        let ResourceClause::Write(segment) = resource else {
            return false;
        };
        segment.state == ContractSegmentState::Current
            && segment.base == read.base
            && (constant_segment_covers_index(&segment.start, &segment.end, &read.index)
                || symbolic_segment_covers_index(
                    &segment.start,
                    &segment.end,
                    &read.index,
                    assumptions,
                    values,
                    array_refs,
                    memory,
                    predicate_environment,
                    click_function_environment,
                ))
    })
}

fn symbolic_segment_covers_index(
    start: &CExpression,
    end: &CExpression,
    index: &CExpression,
    assumptions: &Assumptions,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> bool {
    let lowerer = KernelPropositionLowerer::new(
        values.clone(),
        array_refs.clone(),
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    let Ok(start) = lowerer.lower_requirement_c_expression(start) else {
        return false;
    };
    let Ok(end) = lowerer.lower_requirement_c_expression(end) else {
        return false;
    };
    let Ok(index) = lowerer.lower_requirement_c_expression(index) else {
        return false;
    };
    let Ok(lower_bound) =
        comparison_proposition(start, ComparisonOperator::LessEqual, index.clone())
    else {
        return false;
    };
    let Ok(upper_bound) = comparison_proposition(index, ComparisonOperator::LessThan, end) else {
        return false;
    };
    assumptions.proves(&lower_bound) && assumptions.proves(&upper_bound)
}

fn constant_segment_covers_index(
    start: &CExpression,
    end: &CExpression,
    index: &CExpression,
) -> bool {
    let Some(start) = constant_c_expression_i64(start) else {
        return false;
    };
    let Some(end) = constant_c_expression_i64(end) else {
        return false;
    };
    let Some(index) = constant_c_expression_i64(index) else {
        return false;
    };
    start <= index && index < end
}

fn constant_c_expression_i64(expression: &CExpression) -> Option<i64> {
    match expression {
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
            Some(*value as i32 as i64)
        }
        CExpression::Value(CValue::UInt8(Bitvector32Term::Constant(value))) => {
            Some(i64::from(*value))
        }
        CExpression::Add(left, right) => {
            Some(constant_c_expression_i64(left)? + constant_c_expression_i64(right)?)
        }
        CExpression::Subtract(left, right) => {
            Some(constant_c_expression_i64(left)? - constant_c_expression_i64(right)?)
        }
        _ => None,
    }
}

fn reject_resource_representation_cycles(
    definitions: &[ResourceDefinition],
) -> Result<(), ClickError> {
    let graph = definitions
        .iter()
        .map(|definition| {
            let dependencies = definition
                .representation()
                .into_iter()
                .flat_map(ResourceRepresentation::contains)
                .filter_map(|resource| match resource {
                    ResourceClause::Named { name, .. } => Some(name.clone()),
                    ResourceClause::Read(_)
                    | ResourceClause::Write(_)
                    | ResourceClause::Free(_) => None,
                })
                .collect::<Vec<_>>();
            (definition.name().to_string(), dependencies)
        })
        .collect::<BTreeMap<_, _>>();
    let mut permanent = BTreeSet::new();
    let mut visiting = Vec::new();
    for name in graph.keys() {
        reject_resource_representation_cycles_from(name, &graph, &mut permanent, &mut visiting)?;
    }
    Ok(())
}

fn reject_resource_representation_cycles_from(
    name: &str,
    graph: &BTreeMap<String, Vec<String>>,
    permanent: &mut BTreeSet<String>,
    visiting: &mut Vec<String>,
) -> Result<(), ClickError> {
    if permanent.contains(name) {
        return Ok(());
    }
    if let Some(index) = visiting.iter().position(|candidate| candidate == name) {
        let mut cycle = visiting[index..].to_vec();
        cycle.push(name.to_string());
        return Err(ClickError::new(format!(
            "resource representation cycle: {}",
            cycle.join(" -> ")
        )));
    }
    visiting.push(name.to_string());
    for dependency in graph.get(name).into_iter().flatten() {
        if graph.contains_key(dependency) {
            reject_resource_representation_cycles_from(dependency, graph, permanent, visiting)?;
        }
    }
    visiting.pop();
    permanent.insert(name.to_string());
    Ok(())
}

fn function_signature_type_environment(
    signature: &FunctionSignature,
    include_result: bool,
) -> BTreeMap<String, C0Type> {
    let mut variables = signature
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    if include_result {
        variables.insert("result".to_string(), signature.return_type());
    }
    variables
}

fn theorem_type_environment(theorem: &TheoremDefinition) -> BTreeMap<String, C0Type> {
    theorem
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect()
}

fn validate_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            let _ = infer_contract_expression_type(left, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(())
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_proposition_expression_types(left, variables, click_functions, context)?;
            validate_proposition_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_proposition_expression_types(body, variables, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            let _ = infer_contract_expression_type(start, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(end, variables, click_functions, context)?;
            validate_proposition_expression_types(body, variables, click_functions, context)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                let _ =
                    infer_contract_expression_type(argument, variables, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_pure_theorem_proof(theorem_name: &str, proof: &Proof) -> Result<(), ClickError> {
    match proof {
        Proof::Tactic(Tactic::Auto | Tactic::Simp) => Ok(()),
        Proof::Tactic(Tactic::Frame) => Err(ClickError::new(format!(
            "`frame` cannot prove pure theorem `{theorem_name}`"
        ))),
        Proof::Steps(steps) => {
            for step in steps {
                match step {
                    ProofStep::Unfold(_) | ProofStep::ApplyTheorem(_) | ProofStep::Simp => {}
                    ProofStep::SymbolicExecute
                    | ProofStep::BoundedExecute
                    | ProofStep::LoopVc(_)
                    | ProofStep::Frame(_)
                    | ProofStep::OpenResource(_)
                    | ProofStep::CloseResource(_)
                    | ProofStep::Witness(_)
                    | ProofStep::Choose(_) => {
                        return Err(ClickError::new(format!(
                            "proof step `{}` cannot prove pure theorem `{theorem_name}`",
                            proof_step_name(step)
                        )));
                    }
                }
            }
            Ok(())
        }
    }
}

fn proof_step_name(step: &ProofStep) -> &'static str {
    match step {
        ProofStep::SymbolicExecute => "symbolic_execute",
        ProofStep::BoundedExecute => "bounded_execute",
        ProofStep::LoopVc(_) => "loop_vc",
        ProofStep::Frame(_) => "frame",
        ProofStep::Unfold(_) => "unfold",
        ProofStep::ApplyTheorem(_) => "apply",
        ProofStep::OpenResource(_) => "open",
        ProofStep::CloseResource(_) => "close",
        ProofStep::Witness(_) => "witness",
        ProofStep::Choose(_) => "choose",
        ProofStep::Simp => "simp",
    }
}

fn reject_duplicate_named_resource_clauses<'a>(
    resources: impl IntoIterator<Item = &'a ResourceClause>,
    context: &str,
) -> Result<(), ClickError> {
    let mut seen = Vec::new();
    for resource in resources {
        if !matches!(resource, ResourceClause::Named { .. }) {
            continue;
        }
        if seen.iter().any(|candidate| *candidate == resource) {
            return Err(ClickError::new(format!(
                "duplicate affine resource `{}` in {context}",
                describe_resource_clause(resource)
            )));
        }
        seen.push(resource);
    }
    Ok(())
}

fn describe_resource_clause(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Read(segment) => format!(
            "read({}[{}..{}])",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::Write(segment) => format!(
            "write({}[{}..{}])",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::Free(segment) => format!(
            "free({}[{}..{}])",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::Named {
            name, arguments, ..
        } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn describe_c0_type(c_type: C0Type) -> String {
    match c_type {
        C0Type::Int32 => "int32".to_string(),
        C0Type::UInt8 => "uint8".to_string(),
        C0Type::Int32Pointer | C0Type::Int32Array(_) => "int32*".to_string(),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => "uint8*".to_string(),
    }
}

fn click_types_compatible(actual: C0Type, expected: C0Type) -> bool {
    match (actual, expected) {
        (C0Type::Int32Array(_), C0Type::Int32Pointer)
        | (C0Type::Int32Pointer, C0Type::Int32Array(_)) => true,
        (C0Type::UInt8Array(_), C0Type::UInt8Pointer)
        | (C0Type::UInt8Pointer, C0Type::UInt8Array(_)) => true,
        _ => actual == expected,
    }
}

fn infer_contract_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    match expression {
        ContractExpression::CFragment(expression) => {
            Ok(infer_c_expression_type(expression, variables))
        }
        ContractExpression::Old(expression) | ContractExpression::At { expression, .. } => {
            infer_contract_expression_type(expression, variables, click_functions, context)
        }
        ContractExpression::Add(left, right) => {
            infer_add_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Subtract(left, right) => {
            infer_subtract_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(C0Type::Int32)
                }
                _ => None,
            })
        }
        ContractExpression::BitwiseNot(expression) => {
            let expression =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            Ok(expression
                .filter(|c_type| type_is_scalar(*c_type))
                .map(|_| C0Type::Int32))
        }
        ContractExpression::Index(base, index) => {
            let _ = infer_contract_expression_type(index, variables, click_functions, context)?;
            Ok(
                infer_contract_expression_type(base, variables, click_functions, context)?
                    .and_then(pointer_element_type),
            )
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_type =
                infer_contract_expression_type(then_branch, variables, click_functions, context)?;
            let else_type =
                infer_contract_expression_type(else_branch, variables, click_functions, context)?;
            Ok(match (then_type, else_type) {
                (Some(then_type), Some(else_type))
                    if click_types_compatible(then_type, else_type) =>
                {
                    Some(then_type)
                }
                (Some(_), Some(_)) => None,
                (Some(c_type), None) | (None, Some(c_type)) => Some(c_type),
                (None, None) => None,
            })
        }
        ContractExpression::RangeFold {
            initial,
            accumulator,
            item,
            body,
            ..
        } => {
            let initial_type =
                infer_contract_expression_type(initial, variables, click_functions, context)?;
            let mut body_variables = variables.clone();
            if let Some(initial_type) = initial_type {
                body_variables.insert(accumulator.clone(), initial_type);
            }
            body_variables.insert(item.clone(), C0Type::Int32);
            infer_contract_expression_type(body, &body_variables, click_functions, context)
                .map(|body_type| body_type.or(initial_type))
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value_type =
                infer_contract_expression_type(value, variables, click_functions, context)?;
            if let (Some(expected), Some(actual)) = (*c_type, value_type) {
                if !click_types_compatible(actual, expected) {
                    return Err(ClickError::new(format!(
                        "let binding `{name}` expects {}, got {} in {context}",
                        describe_c0_type(expected),
                        describe_c0_type(actual)
                    )));
                }
            }
            let mut body_variables = variables.clone();
            if let Some(binding_type) = c_type.or(value_type) {
                body_variables.insert(name.clone(), binding_type);
            }
            infer_contract_expression_type(body, &body_variables, click_functions, context)
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(None);
            };
            for (index, (parameter, argument)) in
                function.parameters.iter().zip(arguments).enumerate()
            {
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                {
                    let expected = parameter.c_type();
                    if !click_types_compatible(actual, expected) {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(expected),
                            describe_c0_type(actual)
                        )));
                    }
                }
            }
            Ok(Some(function.return_type))
        }
    }
}

fn infer_c_expression_type(
    expression: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    match expression {
        CExpression::Value(CValue::Int32(_)) => Some(C0Type::Int32),
        CExpression::Value(CValue::UInt8(_)) => Some(C0Type::UInt8),
        CExpression::Value(CValue::Pointer(_)) => None,
        CExpression::Variable(name) => variables.get(name).copied(),
        CExpression::AddressOf(_) => None,
        CExpression::LessThan(_, _)
        | CExpression::LessEqual(_, _)
        | CExpression::GreaterThan(_, _)
        | CExpression::GreaterEqual(_, _)
        | CExpression::Equal(_, _)
        | CExpression::NotEqual(_, _)
        | CExpression::Not(_)
        | CExpression::And(_, _)
        | CExpression::Or(_, _) => Some(C0Type::Int32),
        CExpression::Add(left, right) => infer_c_add_type(left, right, variables),
        CExpression::Subtract(left, right) => infer_c_subtract_type(left, right, variables),
        CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            let left = infer_c_expression_type(left, variables);
            let right = infer_c_expression_type(right, variables);
            match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(C0Type::Int32)
                }
                _ => None,
            }
        }
        CExpression::BitwiseNot(expression) => infer_c_expression_type(expression, variables)
            .filter(|c_type| type_is_scalar(*c_type))
            .map(|_| C0Type::Int32),
        CExpression::Load(pointer) => {
            infer_c_expression_type(pointer, variables).and_then(pointer_element_type)
        }
        CExpression::Index(base, _) => {
            infer_c_expression_type(base, variables).and_then(pointer_element_type)
        }
    }
}

fn infer_add_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(pointer_arithmetic_type(left, right).or_else(|| scalar_arithmetic_type(left, right)))
}

fn infer_subtract_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(match (left, right) {
        (Some(left), Some(right)) if type_is_pointer(left) && type_is_scalar(right) => Some(left),
        _ => scalar_arithmetic_type(left, right),
    })
}

fn infer_c_add_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    pointer_arithmetic_type(left, right).or_else(|| scalar_arithmetic_type(left, right))
}

fn infer_c_subtract_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    match (left, right) {
        (Some(left), Some(right)) if type_is_pointer(left) && type_is_scalar(right) => Some(left),
        _ => scalar_arithmetic_type(left, right),
    }
}

fn pointer_arithmetic_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_pointer(left) && type_is_scalar(right) => Some(left),
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_pointer(right) => Some(right),
        _ => None,
    }
}

fn scalar_arithmetic_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
            Some(C0Type::Int32)
        }
        _ => None,
    }
}

fn type_is_scalar(c_type: C0Type) -> bool {
    matches!(c_type, C0Type::Int32 | C0Type::UInt8)
}

fn type_is_pointer(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int32Pointer | C0Type::UInt8Pointer | C0Type::Int32Array(_) | C0Type::UInt8Array(_)
    )
}

fn pointer_element_type(c_type: C0Type) -> Option<C0Type> {
    match c_type {
        C0Type::Int32Pointer | C0Type::Int32Array(_) => Some(C0Type::Int32),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => Some(C0Type::UInt8),
        C0Type::Int32 | C0Type::UInt8 => None,
    }
}

fn validate_resource_clause(
    resource: &ResourceClause,
    resources: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    variables: &BTreeMap<String, C0Type>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Read(_) | ResourceClause::Write(_) | ResourceClause::Free(_) => Ok(()),
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } => {
            let Some(arity) = resources.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown resource `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            if parameter_types.len() != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata in {context}"
                )));
            }
            for (index, argument) in arguments.iter().enumerate() {
                validate_contract_expression_calls(argument, click_functions, context)?;
                if let Some(actual) = infer_contract_expression_type(
                    argument,
                    variables,
                    click_function_types,
                    context,
                )? {
                    let expected = parameter_types[index];
                    if !click_types_compatible(actual, expected) {
                        return Err(ClickError::new(format!(
                            "resource `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(expected),
                            describe_c0_type(actual)
                        )));
                    }
                }
            }
            Ok(())
        }
    }
}

fn validate_predicate_calls_in_proposition(
    proposition: &ClickProposition,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_predicate_calls_in_proposition(left, predicates, click_functions, context)?;
            validate_predicate_calls_in_proposition(right, predicates, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_predicate_calls_in_proposition(body, predicates, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_predicate_calls_in_proposition(body, predicates, click_functions, context)
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let Some(arity) = predicates.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown predicate `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "predicate `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_click_function_expression(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    if contains_old_expression(expression) {
        return Err(ClickError::new(format!(
            "`old(...)` is not available inside {context}"
        )));
    }
    if contains_at_expression(expression) {
        return Err(ClickError::new(format!(
            "`at(...)` is not available inside {context}"
        )));
    }
    validate_contract_expression_calls(expression, click_functions, context)
}

fn validate_contract_expression_calls(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match expression {
        ContractExpression::CFragment(_) => Ok(()),
        ContractExpression::Old(body) => {
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::At { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
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
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ContractExpression::BitwiseNot(expression) => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_if_condition_proposition(condition, click_functions, context)?;
            validate_contract_expression_calls(then_branch, click_functions, context)?;
            validate_contract_expression_calls(else_branch, click_functions, context)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_contract_expression_calls(initial, click_functions, context)?;
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Let { value, body, .. } => {
            validate_contract_expression_calls(value, click_functions, context)?;
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Call { name, arguments } => {
            let Some(arity) = click_functions.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown function `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "function `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_if_condition_proposition(
    proposition: &ClickProposition,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_if_condition_proposition(left, click_functions, context)?;
            validate_if_condition_proposition(right, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_if_condition_proposition(body, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_if_condition_proposition(body, click_functions, context)
        }
        ClickProposition::PredicateCall { name, .. } => Err(ClickError::new(format!(
            "predicate call `{name}` is not supported in `if` expression condition in {context}"
        ))),
    }
}

fn contains_old_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Old(_) => true,
        ContractExpression::CFragment(_) => false,
        ContractExpression::At { expression, .. } => contains_old_expression(expression),
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
            contains_old_expression(left) || contains_old_expression(right)
        }
        ContractExpression::BitwiseNot(expression) => contains_old_expression(expression),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_old_expression(condition)
                || contains_old_expression(then_branch)
                || contains_old_expression(else_branch)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_old_expression(start)
                || contains_old_expression(end)
                || contains_old_expression(initial)
                || contains_old_expression(body)
        }
        ContractExpression::Let { value, body, .. } => {
            contains_old_expression(value) || contains_old_expression(body)
        }
        ContractExpression::Call { arguments, .. } => arguments.iter().any(contains_old_expression),
    }
}

fn proposition_contains_old_expression(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_contains_old_expression(left) || proposition_contains_old_expression(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => proposition_contains_old_expression(body),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_old_expression(start)
                || contains_old_expression(end)
                || proposition_contains_old_expression(body)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_old_expression)
        }
    }
}

fn contains_at_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::At { .. } => true,
        ContractExpression::CFragment(_) => false,
        ContractExpression::Old(expression) | ContractExpression::BitwiseNot(expression) => {
            contains_at_expression(expression)
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
            contains_at_expression(left) || contains_at_expression(right)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_at_expression(condition)
                || contains_at_expression(then_branch)
                || contains_at_expression(else_branch)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_at_expression(start)
                || contains_at_expression(end)
                || contains_at_expression(initial)
                || contains_at_expression(body)
        }
        ContractExpression::Let { value, body, .. } => {
            contains_at_expression(value) || contains_at_expression(body)
        }
        ContractExpression::Call { arguments, .. } => arguments.iter().any(contains_at_expression),
    }
}

fn proposition_contains_at_expression(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_contains_at_expression(left) || proposition_contains_at_expression(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => proposition_contains_at_expression(body),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_at_expression(start)
                || contains_at_expression(end)
                || proposition_contains_at_expression(body)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_at_expression)
        }
    }
}

fn collect_click_function_calls(expression: &ContractExpression, calls: &mut BTreeSet<String>) {
    match expression {
        ContractExpression::CFragment(_) => {}
        ContractExpression::Old(body) => collect_click_function_calls(body, calls),
        ContractExpression::At { expression, .. } => {
            collect_click_function_calls(expression, calls)
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
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        ContractExpression::BitwiseNot(expression) => {
            collect_click_function_calls(expression, calls)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_function_calls_in_proposition(condition, calls);
            collect_click_function_calls(then_branch, calls);
            collect_click_function_calls(else_branch, calls);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_click_function_calls(start, calls);
            collect_click_function_calls(end, calls);
            collect_click_function_calls(initial, calls);
            collect_click_function_calls(body, calls);
        }
        ContractExpression::Let { value, body, .. } => {
            collect_click_function_calls(value, calls);
            collect_click_function_calls(body, calls);
        }
        ContractExpression::Call { name, arguments } => {
            calls.insert(name.clone());
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

fn collect_click_function_calls_in_proposition(
    proposition: &ClickProposition,
    calls: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_function_calls_in_proposition(left, calls);
            collect_click_function_calls_in_proposition(right, calls);
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            collect_click_function_calls_in_proposition(body, calls);
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_click_function_calls(start, calls);
            collect_click_function_calls(end, calls);
            collect_click_function_calls_in_proposition(body, calls);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

fn reject_recursive_click_functions(
    function_calls: &BTreeMap<String, BTreeSet<String>>,
) -> Result<(), ClickError> {
    fn check_call_dag(
        name: &str,
        function_calls: &BTreeMap<String, BTreeSet<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
    ) -> Result<(), ClickError> {
        if visited.contains(name) {
            return Ok(());
        }
        if !visiting.insert(name.to_string()) {
            return Err(ClickError::new(format!(
                "recursive function definition involving `{name}` is not supported yet"
            )));
        }
        if let Some(calls) = function_calls.get(name) {
            for callee in calls {
                check_call_dag(callee, function_calls, visiting, visited)?;
            }
        }
        visiting.remove(name);
        visited.insert(name.to_string());
        Ok(())
    }

    let mut visited = BTreeSet::new();
    for name in function_calls.keys() {
        check_call_dag(name, function_calls, &mut BTreeSet::new(), &mut visited)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
