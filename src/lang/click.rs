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
    OpenResource(ResourceClause),
    CloseResource(ResourceClause),
    Witness(ProofWitness),
    Choose(ProofChoice),
    Simp,
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
pub enum VerifiedClaim {
    Ensure { index: usize, clause: EnsureClause },
    Effect { index: usize, clause: EffectClause },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProofKind {
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
    Parser::new(source)?.parse_file()
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
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);
    let resource_environment = ResourceEnvironment::new(&resource_definitions);
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
                        steps,
                    )?;
                    verified.extend(theorems);
                }
            }
        }
    }

    Ok(verified)
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
        parsed_function.parameters(),
        &function,
        &state,
        &arguments,
        &requirement_propositions,
        &replay.unfolded_predicates,
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
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    state: &CState,
    arguments: &[CExpression],
    requirement_propositions: &[Proposition],
    unfolded_predicates: &[String],
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

fn is_tactic_name(name: &str) -> bool {
    matches!(name, "auto" | "frame" | "simp")
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Token {
    Ident(String),
    Number(u32),
    CharLiteral(u8),
    String(String),
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Colon,
    Comma,
    Semicolon,
    Dot,
    DotDot,
    Arrow,
    Equal,
    EqualEqual,
    BangEqual,
    LessThan,
    LessEqual,
    ShiftLeft,
    GreaterThan,
    GreaterEqual,
    ShiftRight,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Caret,
    Tilde,
    Pipe,
}

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ContractLetBinding {
    name: String,
    c_type: Option<C0Type>,
    kind: ContractLetBindingKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ContractLetBindingKind {
    Value(ContractExpression),
    Where(ClickProposition),
}

impl ContractLetBinding {
    fn value(&self) -> Option<&ContractExpression> {
        match &self.kind {
            ContractLetBindingKind::Value(value) => Some(value),
            ContractLetBindingKind::Where(_) => None,
        }
    }

    fn where_condition(&self) -> Option<&ClickProposition> {
        match &self.kind {
            ContractLetBindingKind::Value(_) => None,
            ContractLetBindingKind::Where(condition) => Some(condition),
        }
    }
}

impl Parser {
    fn new(source: &str) -> Result<Self, ClickError> {
        Ok(Self {
            tokens: tokenize(source)?,
            position: 0,
        })
    }

    fn parse_file(mut self) -> Result<ClickFile, ClickError> {
        let file = expand_declared_resource_clauses(self.parse_file_items()?)?;
        validate_click_definitions(&file)?;
        Ok(file)
    }

    fn parse_file_items(&mut self) -> Result<ClickFile, ClickError> {
        let mut verifying_sources = Vec::new();
        let mut predicate_definitions = Vec::new();
        let mut click_function_definitions = Vec::new();
        let mut resource_definitions = Vec::new();
        let mut function_blocks = Vec::new();

        while self.peek().is_some() {
            if self.peek_ident() == Some("verifying") {
                verifying_sources.push(self.parse_verifying_source()?);
            } else if self.peek_ident() == Some("predicate") {
                predicate_definitions.push(self.parse_predicate_definition()?);
            } else if self.peek_ident() == Some("function") {
                click_function_definitions.push(self.parse_click_function_definition()?);
            } else if self.peek_ident() == Some("affine")
                && self.peek_next_ident() == Some("resource")
            {
                resource_definitions.push(self.parse_resource_definition()?);
            } else {
                function_blocks.push(self.parse_function_block()?);
            }
        }

        let file = ClickFile {
            verifying_sources,
            predicate_definitions,
            click_function_definitions,
            resource_definitions,
            function_blocks,
        };
        Ok(file)
    }

    fn parse_verifying_source(&mut self) -> Result<String, ClickError> {
        self.expect_ident_spelling("verifying")?;
        let source_path = self.expect_string("C source path")?;
        self.expect(Token::Semicolon)?;
        Ok(source_path)
    }

    fn parse_predicate_definition(&mut self) -> Result<PredicateDefinition, ClickError> {
        self.expect_ident_spelling("predicate")?;
        let name = self.expect_ident("predicate name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;
        let body = self.parse_proposition()?;
        self.expect(Token::RBrace)?;
        Ok(PredicateDefinition {
            name,
            parameters,
            body,
        })
    }

    fn parse_click_function_definition(&mut self) -> Result<ClickFunctionDefinition, ClickError> {
        self.expect_ident_spelling("function")?;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Arrow)?;
        let return_type = self.parse_type()?;
        self.expect(Token::LBrace)?;
        let body = self.parse_contract_expression()?;
        self.expect(Token::RBrace)?;
        Ok(ClickFunctionDefinition {
            name,
            parameters,
            return_type,
            body,
        })
    }

    fn parse_resource_definition(&mut self) -> Result<ResourceDefinition, ClickError> {
        self.expect_ident_spelling("affine")?;
        self.expect_ident_spelling("resource")?;
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_resource_parameters()?;
        self.expect(Token::RParen)?;
        let representation = match self.peek() {
            Some(Token::Semicolon) => {
                self.position += 1;
                None
            }
            Some(Token::LBrace) => Some(self.parse_resource_representation()?),
            Some(token) => {
                return Err(self.error(format!(
                    "expected `;` or resource representation body, got {token:?}"
                )));
            }
            None => {
                return Err(
                    self.error("expected `;` or resource representation body, got end of input")
                );
            }
        };
        Ok(ResourceDefinition {
            name,
            parameters,
            kind: ResourceKind::Affine,
            representation,
        })
    }

    fn parse_resource_representation(&mut self) -> Result<ResourceRepresentation, ClickError> {
        self.expect(Token::LBrace)?;
        let mut contains = Vec::new();
        let mut invariants = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("contains") => {
                    self.position += 1;
                    contains.push(self.parse_resource_clause()?);
                    self.expect(Token::Semicolon)?;
                }
                Some("invariant") => {
                    self.position += 1;
                    invariants.push(self.parse_proposition()?);
                    self.expect(Token::Semicolon)?;
                }
                Some(name) => {
                    return Err(self.error(format!(
                        "expected `contains` or `invariant` in resource body, got `{name}`"
                    )));
                }
                None => {
                    return Err(self.error(
                        "expected `contains` or `invariant` in resource body, got end of input",
                    ));
                }
            }
        }
        self.expect(Token::RBrace)?;
        Ok(ResourceRepresentation {
            contains,
            invariants,
        })
    }

    fn parse_resource_parameters(&mut self) -> Result<Vec<FunctionParameter>, ClickError> {
        let mut parameters = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(parameters);
        }

        loop {
            let name = self.expect_ident("resource parameter name")?;
            self.expect(Token::Colon)?;
            let c_type = self.parse_type()?;
            let c_type = self.parse_parameter_array_suffix(c_type)?;
            parameters.push(FunctionParameter { c_type, name });

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => return Ok(parameters),
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    fn parse_function_block(&mut self) -> Result<FunctionBlock, ClickError> {
        let signature = self.parse_function_signature()?;
        self.expect(Token::LBrace)?;

        let parameter_names = signature
            .parameters()
            .iter()
            .map(|parameter| parameter.name().to_string())
            .collect::<BTreeSet<_>>();
        let mut contract_lets = Vec::new();
        let mut contract_let_names = BTreeSet::new();
        let mut requires = Vec::new();
        let mut structural_clauses = Vec::new();
        let mut structural_labels = BTreeSet::new();
        let mut effects = Vec::new();
        let mut ensures = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            match self.peek_ident() {
                Some("let") => {
                    let binding = self.parse_contract_let_binding()?;
                    if parameter_names.contains(binding.name.as_str()) {
                        return Err(self.error(format!(
                            "contract `let` `{}` conflicts with a C parameter in `{}`",
                            binding.name,
                            signature.name()
                        )));
                    }
                    if !contract_let_names.insert(binding.name.clone()) {
                        return Err(self.error(format!(
                            "duplicate contract `let` `{}` in `{}`",
                            binding.name,
                            signature.name()
                        )));
                    }
                    let substitutions = contract_let_substitutions(&contract_lets);
                    let kind = match binding.kind {
                        ContractLetBindingKind::Value(value) => ContractLetBindingKind::Value(
                            substitute_contract_expression(&value, &substitutions)
                                .map_err(|message| self.error(message))?,
                        ),
                        ContractLetBindingKind::Where(condition) => {
                            ContractLetBindingKind::Where(condition)
                        }
                    };
                    contract_lets.push(ContractLetBinding { kind, ..binding });
                }
                Some("requires") => {
                    let requirement = self.parse_requirement()?;
                    requires.push(
                        apply_contract_lets_to_requirement(requirement, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("for") => {
                    let clause = self.parse_structural_clause()?;
                    if let Some(label) = clause.label() {
                        if matches!(label, "function" | "loop" | "statement") {
                            return Err(self.error(format!(
                                "`{label}` is reserved and cannot be used as a code region label"
                            )));
                        }
                        if !structural_labels.insert(label.to_string()) {
                            return Err(self.error(format!(
                                "duplicate code region label `{label}` in `{}`",
                                signature.name()
                            )));
                        }
                    }
                    structural_clauses.push(
                        apply_contract_lets_to_structural_clause(clause, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("immutable" | "mutable" | "mutable_field") => {
                    let effect = self.parse_effect_clause()?;
                    effects.push(
                        apply_contract_lets_to_effect_clause(effect, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some("ensures") => {
                    let ensure = self.parse_ensure_clause()?;
                    ensures.push(
                        apply_contract_lets_to_ensure_clause(ensure, &contract_lets)
                            .map_err(|message| self.error(message))?,
                    );
                }
                Some(keyword) => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `immutable`, `mutable`, `mutable_field`, `for`, `ensures`, or `}}` in `{}`, got `{keyword}`",
                        signature.name()
                    )));
                }
                None => {
                    return Err(self.error(format!(
                        "expected `let`, `requires`, `immutable`, `mutable`, `mutable_field`, `for`, `ensures`, or `}}` in `{}`",
                        signature.name()
                    )));
                }
            }
        }
        self.expect(Token::RBrace)?;

        Ok(FunctionBlock {
            signature,
            requires,
            structural_clauses,
            effects,
            ensures,
        })
    }

    fn parse_contract_let_binding(&mut self) -> Result<ContractLetBinding, ClickError> {
        self.expect_ident_spelling("let")?;
        let name = self.expect_ident("let binding name")?;
        let c_type = if self.peek() == Some(&Token::Colon) {
            self.position += 1;
            Some(self.parse_type()?)
        } else {
            None
        };
        let kind = if self.peek() == Some(&Token::Equal) {
            self.position += 1;
            ContractLetBindingKind::Value(self.parse_contract_expression()?)
        } else if self.peek_ident() == Some("where") {
            self.position += 1;
            if c_type.is_none() {
                return Err(self.error("`let ... where` requires an explicit type annotation"));
            }
            ContractLetBindingKind::Where(self.parse_proposition()?)
        } else {
            return Err(self.error("expected `=` or `where` in `let` binding"));
        };
        self.expect(Token::Semicolon)?;
        Ok(ContractLetBinding { name, c_type, kind })
    }

    fn parse_function_signature(&mut self) -> Result<FunctionSignature, ClickError> {
        let return_type = self.parse_type()?;
        let name = self.expect_ident("function name")?;
        self.expect(Token::LParen)?;
        let parameters = self.parse_parameters()?;
        self.expect(Token::RParen)?;

        Ok(FunctionSignature {
            return_type,
            name,
            parameters,
        })
    }

    fn parse_parameters(&mut self) -> Result<Vec<FunctionParameter>, ClickError> {
        let mut parameters = Vec::new();
        if self.peek() == Some(&Token::RParen) {
            return Ok(parameters);
        }

        loop {
            let c_type = self.parse_type()?;
            let name = self.expect_ident("parameter name")?;
            let c_type = self.parse_parameter_array_suffix(c_type)?;
            parameters.push(FunctionParameter { c_type, name });

            match self.peek() {
                Some(Token::Comma) => {
                    self.position += 1;
                }
                Some(Token::RParen) => return Ok(parameters),
                Some(token) => {
                    return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                }
                None => return Err(self.error("expected `,` or `)`, got end of input")),
            }
        }
    }

    fn parse_type(&mut self) -> Result<C0Type, ClickError> {
        let spelling = self.expect_ident("type")?;
        if spelling == "struct" {
            let _struct_name = self.expect_ident("struct name")?;
            if self.peek() == Some(&Token::Star) {
                self.position += 1;
                return Ok(C0Type::Int32Pointer);
            }
            return Err(self.error("only pointer-to-struct types are supported"));
        }

        let scalar_type = match spelling.as_str() {
            "int32" => C0Type::Int32,
            "uint8" => C0Type::UInt8,
            _ => {
                return Err(self.error(format!(
                    "expected type `int32` or `uint8`, got `{spelling}`"
                )));
            }
        };
        if self.peek() == Some(&Token::Star) {
            self.position += 1;
            Ok(match scalar_type {
                C0Type::Int32 => C0Type::Int32Pointer,
                C0Type::UInt8 => C0Type::UInt8Pointer,
                _ => unreachable!("scalar type should not be aggregate"),
            })
        } else {
            Ok(scalar_type)
        }
    }

    fn parse_parameter_array_suffix(&mut self, c_type: C0Type) -> Result<C0Type, ClickError> {
        if self.peek() != Some(&Token::LBracket) {
            return Ok(c_type);
        }
        let pointer_type = match c_type {
            C0Type::Int32 => C0Type::Int32Pointer,
            C0Type::UInt8 => C0Type::UInt8Pointer,
            _ => return Err(self.error("only scalar array parameters are supported")),
        };

        self.position += 1;
        if matches!(self.peek(), Some(Token::Number(_))) {
            self.position += 1;
        }
        self.expect(Token::RBracket)?;
        Ok(pointer_type)
    }

    fn parse_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("requires")?;
        let label = if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next() == Some(&Token::Colon)
        {
            let label = self.expect_ident("requirement label")?;
            self.expect(Token::Colon)?;
            Some(label)
        } else {
            None
        };
        let requirement = match (self.peek_ident(), self.peek_next()) {
            (Some("valid_range"), Some(Token::LParen)) => self.parse_valid_range_requirement()?,
            (Some("valid_field"), Some(Token::LParen)) => self.parse_valid_field_requirement()?,
            (Some("disjoint"), Some(Token::LParen)) => self.parse_disjoint_requirement()?,
            (Some("read") | Some("write") | Some("free"), Some(Token::LParen)) => {
                Requirement::Resource(self.parse_resource_clause()?)
            }
            _ => {
                let proposition = self.parse_proposition()?;
                self.expect(Token::Semicolon)?;
                Requirement::Proposition(proposition)
            }
        };
        if !matches!(requirement, Requirement::Proposition(_)) {
            self.expect(Token::Semicolon)?;
        }
        Ok(if let Some(label) = label {
            Requirement::Labeled {
                label,
                requirement: Box::new(requirement),
            }
        } else {
            requirement
        })
    }

    fn parse_valid_range_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("valid_range")?;
        self.expect(Token::LParen)?;
        let requirement = if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next() == Some(&Token::Comma)
        {
            let name = self.expect_ident("range base name")?;
            self.expect(Token::Comma)?;
            let bytes = self.parse_range_bytes()?;
            Requirement::ValidRange { name, bytes }
        } else {
            let segment = self.parse_current_contract_segment()?;
            Requirement::ValidRangeSegment { segment }
        };
        self.expect(Token::RParen)?;
        Ok(requirement)
    }

    fn parse_valid_field_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("valid_field")?;
        self.expect(Token::LParen)?;
        let field = self.parse_ensure_expression()?;
        self.expect(Token::RParen)?;

        let C0Expression::Load(base) = field else {
            return Err(self.error("`valid_field` expects a field access like `obj->field`"));
        };
        let C0Expression::Variable(name) = *base else {
            return Err(self.error("`valid_field` currently supports pointer parameters only"));
        };

        Ok(Requirement::ValidRange {
            name,
            bytes: RangeBytes::Constant(4),
        })
    }

    fn parse_disjoint_requirement(&mut self) -> Result<Requirement, ClickError> {
        self.expect_ident_spelling("disjoint")?;
        self.expect(Token::LParen)?;
        let left = self.parse_current_contract_segment()?;
        self.expect(Token::Comma)?;
        let right = self.parse_current_contract_segment()?;
        self.expect(Token::RParen)?;
        Ok(Requirement::Disjoint { left, right })
    }

    fn parse_resource_clause(&mut self) -> Result<ResourceClause, ClickError> {
        let name = self.expect_ident("resource name")?;
        self.expect(Token::LParen)?;
        let segment = self.parse_current_contract_segment()?;
        self.expect(Token::RParen)?;
        match name.as_str() {
            "read" => Ok(ResourceClause::Read(segment)),
            "write" => Ok(ResourceClause::Write(segment)),
            "free" => Ok(ResourceClause::Free(segment)),
            _ => Err(self.error(format!("unknown resource `{name}`"))),
        }
    }

    fn parse_range_bytes(&mut self) -> Result<RangeBytes, ClickError> {
        self.parse_range_bytes_add()
    }

    fn parse_range_bytes_add(&mut self) -> Result<RangeBytes, ClickError> {
        let mut expression = self.parse_range_bytes_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_range_bytes_multiply()?;
                    RangeBytes::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_range_bytes_multiply()?;
                    RangeBytes::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_range_bytes_multiply(&mut self) -> Result<RangeBytes, ClickError> {
        let mut expression = self.parse_range_bytes_primary()?;
        while self.peek() == Some(&Token::Star) {
            self.position += 1;
            let right = self.parse_range_bytes_primary()?;
            expression = RangeBytes::Multiply(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_range_bytes_primary(&mut self) -> Result<RangeBytes, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(RangeBytes::Parameter(name)),
            Some(Token::Number(value)) => Ok(RangeBytes::Constant(value)),
            Some(Token::LParen) => {
                let expression = self.parse_range_bytes()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!(
                "expected valid_range byte expression, got {token:?}"
            ))),
            None => Err(self.error("expected valid_range byte expression, got end of input")),
        }
    }

    fn parse_structural_clause(&mut self) -> Result<StructuralClause, ClickError> {
        self.expect_ident_spelling("for")?;
        let region = self.parse_structural_code_region()?;
        let label = if self.peek_ident() == Some("as") {
            self.position += 1;
            Some(self.expect_ident("code region label")?)
        } else {
            None
        };
        self.expect(Token::LBrace)?;
        let mut items = Vec::new();
        while self.peek() != Some(&Token::RBrace) {
            items.extend(self.parse_structural_items()?);
        }
        self.expect(Token::RBrace)?;
        if items.is_empty() {
            return Err(self.error("structural proof block must contain at least one item"));
        }
        Ok(StructuralClause {
            region,
            label,
            items,
        })
    }

    fn parse_structural_code_region(&mut self) -> Result<CodeRegion, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "loop" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("loop index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegion::Loop(index))
            }
            Some(Token::Ident(kind)) if kind == "statement" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("statement index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegion::Statement(index))
            }
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected `loop(N)` or `statement(N)`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected `loop(N)` or `statement(N)`, got {token:?}"
            ))),
            None => Err(self.error("expected `loop(N)` or `statement(N)`, got end of input")),
        }
    }

    fn parse_structural_items(&mut self) -> Result<Vec<StructuralItem>, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "invariant" || kind == "assert" => {
                let item_kind = if kind == "invariant" {
                    StructuralItemKind::Invariant
                } else {
                    StructuralItemKind::Assert
                };
                let proposition = self.parse_proposition()?;
                let proof = self.parse_proof_clause_or_default()?;
                Ok(vec![StructuralItem {
                    kind: item_kind,
                    claim: StructuralItemClaim::Proposition(proposition),
                    proof,
                }])
            }
            Some(Token::Ident(kind))
                if kind == "immutable" || kind == "mutable" || kind == "mutable_field" =>
            {
                let effect = self.parse_effect_after_keyword(kind)?;
                let proof = self.parse_proof_clause_or_default()?;
                Ok(vec![StructuralItem {
                    kind: StructuralItemKind::Effect,
                    claim: StructuralItemClaim::Effect(effect),
                    proof,
                }])
            }
            Some(Token::Ident(kind)) if kind == "step" => {
                self.expect(Token::LBrace)?;
                let mut items = Vec::new();
                while self.peek() != Some(&Token::RBrace) {
                    let effect_kind = self.expect_ident("step effect")?;
                    if effect_kind != "immutable"
                        && effect_kind != "mutable"
                        && effect_kind != "mutable_field"
                    {
                        return Err(self.error(format!(
                            "expected `immutable`, `mutable`, or `mutable_field` inside `step`, got `{effect_kind}`"
                        )));
                    }
                    let effect = self.parse_effect_after_keyword(effect_kind)?;
                    let proof = self.parse_proof_clause_or_default()?;
                    items.push(StructuralItem {
                        kind: StructuralItemKind::StepEffect,
                        claim: StructuralItemClaim::Effect(effect),
                        proof,
                    });
                }
                self.expect(Token::RBrace)?;
                if items.is_empty() {
                    return Err(self.error("`step` block must contain at least one effect"));
                }
                Ok(items)
            }
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected `invariant`, `assert`, `immutable`, `mutable`, `mutable_field`, or `step`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected `invariant`, `assert`, `immutable`, `mutable`, `mutable_field`, or `step`, got {token:?}"
            ))),
            None => Err(self.error(
                "expected `invariant`, `assert`, `immutable`, `mutable`, `mutable_field`, or `step`, got end of input",
            )),
        }
    }

    fn parse_effect_clause(&mut self) -> Result<EffectClause, ClickError> {
        let effect = match self.next() {
            Some(Token::Ident(kind))
                if kind == "immutable" || kind == "mutable" || kind == "mutable_field" =>
            {
                self.parse_effect_after_keyword(kind)?
            }
            Some(Token::Ident(kind)) => {
                return Err(self.error(format!(
                    "expected `immutable`, `mutable`, or `mutable_field`, got `{kind}`"
                )));
            }
            Some(token) => {
                return Err(self.error(format!(
                    "expected `immutable`, `mutable`, or `mutable_field`, got {token:?}"
                )));
            }
            None => {
                return Err(self.error(
                    "expected `immutable`, `mutable`, or `mutable_field`, got end of input",
                ));
            }
        };
        let proof = self.parse_proof_clause_or_default()?;
        Ok(EffectClause { effect, proof })
    }

    fn parse_effect_after_keyword(&mut self, kind: String) -> Result<Effect, ClickError> {
        if kind == "immutable" {
            return Ok(Effect::Immutable);
        }

        if kind == "mutable_field" {
            return self.parse_mutable_field_effect();
        }

        let mut segments = vec![self.parse_contract_segment()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            segments.push(self.parse_contract_segment()?);
        }
        Ok(Effect::Mutable(segments))
    }

    fn parse_mutable_field_effect(&mut self) -> Result<Effect, ClickError> {
        let mut segments = vec![self.parse_current_field_segment()?];
        while self.peek() == Some(&Token::Comma) {
            self.position += 1;
            segments.push(self.parse_current_field_segment()?);
        }
        Ok(Effect::Mutable(segments))
    }

    fn parse_current_field_segment(&mut self) -> Result<ContractSegment, ClickError> {
        self.expect(Token::LParen)?;
        let field = self.parse_ensure_expression()?;
        self.expect(Token::RParen)?;

        let C0Expression::Load(base) = field else {
            return Err(self.error("`mutable_field` expects a field access like `obj->field`"));
        };

        Ok(ContractSegment {
            state: ContractSegmentState::Current,
            base: base.to_kernel_expression(),
            start: C0Expression::Int32Literal(0).to_kernel_expression(),
            end: C0Expression::Int32Literal(1).to_kernel_expression(),
        })
    }

    fn parse_ensure_clause(&mut self) -> Result<EnsureClause, ClickError> {
        self.expect_ident_spelling("ensures")?;
        let name = if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_next() == Some(&Token::Colon)
        {
            let name = self.expect_ident("ensure name")?;
            self.expect(Token::Colon)?;
            Some(name)
        } else {
            None
        };
        let ensure = self.parse_ensure_condition()?;
        let proof = self.parse_proof_clause_or_default()?;

        Ok(EnsureClause {
            name,
            ensure,
            proof,
        })
    }

    fn parse_ensure_condition(&mut self) -> Result<Ensure, ClickError> {
        if matches!(self.peek_ident(), Some("read" | "write" | "free"))
            && self.peek_next() == Some(&Token::LParen)
        {
            return Ok(Ensure::Resource(self.parse_resource_clause()?));
        }
        Ok(Ensure::Proposition(self.parse_proposition()?))
    }

    fn parse_proposition(&mut self) -> Result<ClickProposition, ClickError> {
        self.parse_proposition_implies()
    }

    fn parse_proposition_implies(&mut self) -> Result<ClickProposition, ClickError> {
        let left = self.parse_proposition_or()?;
        if self.peek_ident() == Some("implies") {
            self.position += 1;
            let right = self.parse_proposition_implies()?;
            Ok(ClickProposition::Implies(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_proposition_or(&mut self) -> Result<ClickProposition, ClickError> {
        let mut proposition = self.parse_proposition_and()?;
        while self.peek_ident() == Some("or") {
            self.position += 1;
            let right = self.parse_proposition_and()?;
            proposition = ClickProposition::Or(Box::new(proposition), Box::new(right));
        }
        Ok(proposition)
    }

    fn parse_proposition_and(&mut self) -> Result<ClickProposition, ClickError> {
        let mut proposition = self.parse_proposition_not()?;
        while self.peek_ident() == Some("and") {
            self.position += 1;
            let right = self.parse_proposition_not()?;
            proposition = ClickProposition::And(Box::new(proposition), Box::new(right));
        }
        Ok(proposition)
    }

    fn parse_proposition_not(&mut self) -> Result<ClickProposition, ClickError> {
        if self.peek_ident() == Some("not") {
            self.position += 1;
            Ok(ClickProposition::Not(Box::new(
                self.parse_proposition_not()?,
            )))
        } else {
            self.parse_proposition_atom()
        }
    }

    fn parse_proposition_atom(&mut self) -> Result<ClickProposition, ClickError> {
        if self.peek_ident() == Some("let") {
            let start = self.position;
            let binding = self.parse_contract_let_binding()?;
            let ContractLetBindingKind::Where(condition) = binding.kind else {
                self.position = start;
                return self.parse_proposition_comparison();
            };
            let Some(c_type) = binding.c_type else {
                unreachable!("`let ... where` parser requires an explicit type")
            };
            let body = self.parse_proposition()?;
            return Ok(ClickProposition::Exists {
                c_type,
                name: binding.name,
                body: Box::new(ClickProposition::And(Box::new(condition), Box::new(body))),
            });
        }

        if self.peek_ident() == Some("forall") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let c_type = self.parse_type()?;
            let name = self.expect_ident("forall variable name")?;
            self.expect(Token::RParen)?;
            self.expect(Token::LBrace)?;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            return Ok(ClickProposition::ForAll {
                c_type,
                name,
                body: Box::new(body),
            });
        }

        if self.peek_ident() == Some("exists") {
            self.position += 1;
            self.expect(Token::LParen)?;
            let c_type = self.parse_type()?;
            let name = self.expect_ident("exists variable name")?;
            self.expect(Token::RParen)?;
            self.expect(Token::LBrace)?;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            return Ok(ClickProposition::Exists {
                c_type,
                name,
                body: Box::new(body),
            });
        }

        if self.peek() == Some(&Token::LParen) {
            let start = self.position;
            match self.parse_range_proposition_method() {
                Ok(proposition) => return Ok(proposition),
                Err(_) => {
                    self.position = start;
                }
            }
        }

        if self.peek() == Some(&Token::LParen) {
            let start = self.position;
            self.position += 1;
            let grouped = self.parse_proposition().and_then(|proposition| {
                self.expect(Token::RParen)?;
                Ok(proposition)
            });
            if grouped.is_ok() {
                return grouped;
            }
            self.position = start;
        }

        if matches!(self.peek(), Some(Token::Ident(_)))
            && self.peek_ident() != Some("old")
            && self.peek_ident() != Some("at")
            && self.peek_next() == Some(&Token::LParen)
        {
            let start = self.position;
            let (name, arguments) = self.parse_call_arguments("predicate or function name")?;
            match self.peek() {
                Some(
                    Token::EqualEqual
                    | Token::BangEqual
                    | Token::LessThan
                    | Token::LessEqual
                    | Token::GreaterThan
                    | Token::GreaterEqual,
                ) => {
                    let operator = self.parse_comparison_operator("proposition")?;
                    let right = self.parse_contract_expression()?;
                    return Ok(ClickProposition::Comparison {
                        left: ContractExpression::Call { name, arguments },
                        operator,
                        right,
                    });
                }
                Some(
                    Token::Plus
                    | Token::Minus
                    | Token::Star
                    | Token::Slash
                    | Token::Percent
                    | Token::ShiftLeft
                    | Token::ShiftRight
                    | Token::Amp
                    | Token::Pipe
                    | Token::Caret
                    | Token::LBracket,
                ) => {
                    self.position = start;
                    return self.parse_proposition_comparison();
                }
                _ => return Ok(ClickProposition::PredicateCall { name, arguments }),
            }
        }

        self.parse_proposition_comparison()
    }

    fn parse_range_proposition_method(&mut self) -> Result<ClickProposition, ClickError> {
        self.expect(Token::LParen)?;
        let start = self.parse_contract_expression()?;
        self.expect(Token::DotDot)?;
        let end = self.parse_contract_expression()?;
        self.expect(Token::RParen)?;
        self.expect(Token::Dot)?;
        let method = self.expect_ident("range proposition method")?;
        if method != "all" && method != "any" {
            return Err(self.error(format!(
                "unsupported range proposition method `{method}`; expected `all` or `any`"
            )));
        }

        self.expect(Token::LParen)?;
        self.expect(Token::Pipe)?;
        let item = self.expect_ident("range item name")?;
        self.expect(Token::Pipe)?;
        let body = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let body = self.parse_proposition()?;
            self.expect(Token::RBrace)?;
            body
        } else {
            self.parse_proposition()?
        };
        self.expect(Token::RParen)?;

        match method.as_str() {
            "all" => Ok(ClickProposition::RangeAll {
                start,
                end,
                item,
                body: Box::new(body),
            }),
            "any" => Ok(ClickProposition::RangeAny {
                start,
                end,
                item,
                body: Box::new(body),
            }),
            _ => unreachable!("range proposition method checked above"),
        }
    }

    fn parse_call_arguments(
        &mut self,
        expected_name: &str,
    ) -> Result<(String, Vec<ContractExpression>), ClickError> {
        let name = self.expect_ident(expected_name)?;
        self.expect(Token::LParen)?;
        let mut arguments = Vec::new();
        if self.peek() != Some(&Token::RParen) {
            loop {
                arguments.push(self.parse_contract_expression()?);
                match self.peek() {
                    Some(Token::Comma) => {
                        self.position += 1;
                    }
                    Some(Token::RParen) => break,
                    Some(token) => {
                        return Err(self.error(format!("expected `,` or `)`, got {token:?}")));
                    }
                    None => return Err(self.error("expected `,` or `)`, got end of input")),
                }
            }
        }
        self.expect(Token::RParen)?;
        Ok((name, arguments))
    }

    fn parse_proposition_comparison(&mut self) -> Result<ClickProposition, ClickError> {
        let left = self.parse_contract_expression()?;
        let operator = self.parse_comparison_operator("proposition")?;
        let right = self.parse_contract_expression()?;

        Ok(ClickProposition::Comparison {
            left,
            operator,
            right,
        })
    }

    fn parse_comparison_operator(
        &mut self,
        clause: &str,
    ) -> Result<ComparisonOperator, ClickError> {
        let operator = self.next().ok_or_else(|| {
            self.error(format!(
                "expected comparison operator in `{clause}`, got end of input"
            ))
        })?;

        match operator {
            Token::LessThan => Ok(ComparisonOperator::LessThan),
            Token::LessEqual => Ok(ComparisonOperator::LessEqual),
            Token::GreaterThan => Ok(ComparisonOperator::GreaterThan),
            Token::GreaterEqual => Ok(ComparisonOperator::GreaterEqual),
            Token::EqualEqual => Ok(ComparisonOperator::Equal),
            Token::BangEqual => Ok(ComparisonOperator::NotEqual),
            token => Err(self.error(format!(
                "expected comparison operator in `{clause}`, got {token:?}"
            ))),
        }
    }

    fn parse_by_clause(&mut self) -> Result<Proof, ClickError> {
        self.expect_ident_spelling("by")?;
        if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let proof = match self.peek() {
                Some(Token::Ident(name))
                    if is_tactic_name(name) && self.peek_next() == Some(&Token::Semicolon) =>
                {
                    let tactic = self.parse_tactic()?;
                    self.expect(Token::RBrace)?;
                    Proof::Tactic(tactic)
                }
                Some(Token::RBrace) => {
                    return Err(
                        self.error("`by` block must contain at least one proof step or tactic")
                    );
                }
                Some(_) => {
                    let mut steps = Vec::new();
                    while self.peek() != Some(&Token::RBrace) {
                        steps.push(self.parse_proof_step()?);
                    }
                    self.expect(Token::RBrace)?;
                    Proof::Steps(steps)
                }
                None => return Err(self.error("expected proof step or tactic, got end of input")),
            };
            return Ok(proof);
        }

        Ok(Proof::Tactic(self.parse_tactic()?))
    }

    fn parse_proof_clause_or_default(&mut self) -> Result<Proof, ClickError> {
        if self.peek_ident() == Some("by") {
            self.parse_by_clause()
        } else {
            self.expect(Token::Semicolon)?;
            Ok(Proof::Tactic(Tactic::Auto))
        }
    }

    fn parse_proof_step(&mut self) -> Result<ProofStep, ClickError> {
        let name = self.expect_ident("proof step")?;
        let step = match name.as_str() {
            "symbolic_execute" => {
                self.expect_empty_step_args(&name)?;
                ProofStep::SymbolicExecute
            }
            "bounded_execute" => {
                self.expect_empty_step_args(&name)?;
                ProofStep::BoundedExecute
            }
            "loop_vc" => {
                self.expect(Token::LParen)?;
                let region_ref = self.parse_code_region_ref()?;
                self.expect(Token::RParen)?;
                ProofStep::LoopVc(region_ref)
            }
            "frame" => {
                self.expect(Token::LParen)?;
                let region_ref = if self.peek() == Some(&Token::RParen) {
                    None
                } else {
                    Some(self.parse_code_region_ref()?)
                };
                self.expect(Token::RParen)?;
                ProofStep::Frame(region_ref)
            }
            "unfold" => {
                self.expect(Token::LParen)?;
                let predicate = self.expect_ident("predicate name")?;
                self.expect(Token::RParen)?;
                ProofStep::Unfold(predicate)
            }
            "open" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_named_resource_call()?;
                self.expect(Token::RParen)?;
                ProofStep::OpenResource(resource)
            }
            "witness" => {
                self.expect(Token::LParen)?;
                let name = self.expect_ident("witness variable name")?;
                self.expect(Token::Equal)?;
                let value = self.parse_contract_expression()?;
                self.expect(Token::RParen)?;
                ProofStep::Witness(ProofWitness { name, value })
            }
            "choose" => {
                self.expect(Token::LParen)?;
                let name = self.expect_ident("chosen variable name")?;
                self.expect_ident_spelling("from")?;
                let source = self.parse_proof_fact_source()?;
                self.expect(Token::RParen)?;
                ProofStep::Choose(ProofChoice { name, source })
            }
            "simp" => {
                self.expect_empty_step_args(&name)?;
                ProofStep::Simp
            }
            "close" => {
                self.expect(Token::LParen)?;
                let resource = self.parse_named_resource_call()?;
                self.expect(Token::RParen)?;
                ProofStep::CloseResource(resource)
            }
            _ if is_tactic_name(&name) => {
                return Err(self.error(format!(
                    "`{name}` is a tactic, not a deterministic proof step; use `by {name};` or an explicit proof-step script"
                )));
            }
            _ => return Err(self.error(format!("unknown proof step `{name}`"))),
        };
        self.expect(Token::Semicolon)?;
        Ok(step)
    }

    fn parse_named_resource_call(&mut self) -> Result<ResourceClause, ClickError> {
        let (name, arguments) = self.parse_call_arguments("resource name")?;
        Ok(ResourceClause::Named {
            name,
            arguments,
            parameter_types: Vec::new(),
        })
    }

    fn expect_empty_step_args(&mut self, name: &str) -> Result<(), ClickError> {
        self.expect(Token::LParen)?;
        if self.peek() != Some(&Token::RParen) {
            return Err(self.error(format!("`{name}` expects no arguments")));
        }
        self.expect(Token::RParen)
    }

    fn parse_proof_fact_source(&mut self) -> Result<ProofFactSource, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "requirement" => match self.next() {
                Some(Token::Number(index)) => {
                    let index = usize::try_from(index)
                        .map_err(|_| self.error("requirement index does not fit in usize"))?;
                    Ok(ProofFactSource::Requirement(index))
                }
                Some(Token::Ident(label)) => Ok(ProofFactSource::RequirementLabel(label)),
                Some(token) => Err(self.error(format!(
                    "expected requirement index or label, got {token:?}"
                ))),
                None => Err(self.error("expected requirement index or label, got end of input")),
            },
            Some(Token::Ident(kind)) => Err(self.error(format!(
                "expected proof fact source `requirement N` or `requirement name`, got `{kind}`"
            ))),
            Some(token) => Err(self.error(format!(
                "expected proof fact source `requirement N` or `requirement name`, got {token:?}"
            ))),
            None => Err(self.error("expected proof fact source `requirement N`, got end of input")),
        }
    }

    fn parse_code_region_ref(&mut self) -> Result<CodeRegionRef, ClickError> {
        match self.next() {
            Some(Token::Ident(kind)) if kind == "function" => Ok(CodeRegionRef::Function),
            Some(Token::Ident(kind)) if kind == "loop" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("loop index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Loop(index))
            }
            Some(Token::Ident(kind)) if kind == "statement" => {
                self.expect(Token::LParen)?;
                let index = self.expect_index("statement index")?;
                self.expect(Token::RParen)?;
                Ok(CodeRegionRef::Statement(index))
            }
            Some(Token::Ident(label)) => Ok(CodeRegionRef::Label(label)),
            Some(token) => Err(self.error(format!(
                "expected code region `function`, `loop(N)`, `statement(N)`, or label, got {token:?}"
            ))),
            None => Err(self.error(
                "expected code region `function`, `loop(N)`, `statement(N)`, or label, got end of input",
            )),
        }
    }

    fn parse_tactic(&mut self) -> Result<Tactic, ClickError> {
        let tactic = match self.next() {
            Some(Token::Ident(name)) if name == "auto" => Tactic::Auto,
            Some(Token::Ident(name)) if name == "frame" => Tactic::Frame,
            Some(Token::Ident(name)) if name == "simp" => Tactic::Simp,
            Some(Token::Ident(name)) => {
                return Err(self.error(format!("expected tactic, got `{name}`")));
            }
            Some(token) => {
                return Err(self.error(format!("expected tactic, got {token:?}")));
            }
            None => return Err(self.error("expected tactic, got end of input")),
        };
        self.expect(Token::Semicolon)?;
        Ok(tactic)
    }

    fn parse_ensure_expression(&mut self) -> Result<C0Expression, ClickError> {
        self.parse_ensure_bitwise_or()
    }

    fn parse_contract_expression(&mut self) -> Result<ContractExpression, ClickError> {
        self.parse_contract_bitwise_or()
    }

    fn parse_contract_segment(&mut self) -> Result<ContractSegment, ClickError> {
        if self.peek_ident() == Some("old") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let mut segment = self.parse_current_contract_segment()?;
            segment.state = ContractSegmentState::Old;
            self.expect(Token::RParen)?;
            return Ok(segment);
        }

        self.parse_current_contract_segment()
    }

    fn parse_current_contract_segment(&mut self) -> Result<ContractSegment, ClickError> {
        let base = self.parse_ensure_primary()?.to_kernel_expression();
        self.expect(Token::LBracket)?;
        let start = self.parse_ensure_expression()?.to_kernel_expression();
        self.expect(Token::DotDot)?;
        let end = self.parse_ensure_expression()?.to_kernel_expression();
        self.expect(Token::RBracket)?;
        Ok(ContractSegment {
            state: ContractSegmentState::Current,
            base,
            start,
            end,
        })
    }

    fn parse_contract_bitwise_or(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_contract_bitwise_xor()?;
            expression = ContractExpression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_bitwise_xor(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_contract_bitwise_and()?;
            expression = ContractExpression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_bitwise_and(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_shift()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_contract_shift()?;
            expression = ContractExpression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_shift(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_contract_add()?;
                    ContractExpression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_contract_add()?;
                    ContractExpression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_contract_add(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_contract_multiply()?;
                    ContractExpression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_contract_multiply()?;
                    ContractExpression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_contract_multiply(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_unary()?;
        loop {
            let Some(operator) = self.peek() else {
                break;
            };
            let constructor = match operator {
                Token::Star => ContractExpression::Multiply,
                Token::Slash => ContractExpression::Divide,
                Token::Percent => ContractExpression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_contract_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_contract_unary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(ContractExpression::BitwiseNot(Box::new(
                self.parse_contract_unary()?,
            )));
        }

        self.parse_contract_postfix()
    }

    fn parse_contract_postfix(&mut self) -> Result<ContractExpression, ClickError> {
        let mut expression = self.parse_contract_primary()?;
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_contract_expression()?;
                    self.expect(Token::RBracket)?;
                    expression = ContractExpression::Index(Box::new(expression), Box::new(index));
                }
                Some(Token::Arrow) => {
                    self.position += 1;
                    let _field_name = self.expect_ident("field name")?;
                    let Some(base) = contract_expression_as_c_fragment(&expression) else {
                        return Err(
                            self.error("field access is only supported on current C fragments")
                        );
                    };
                    expression = ContractExpression::CFragment(CExpression::Load(Box::new(base)));
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_contract_primary(&mut self) -> Result<ContractExpression, ClickError> {
        if self.peek_ident() == Some("let") {
            let binding = self.parse_contract_let_binding()?;
            let ContractLetBindingKind::Value(value) = binding.kind else {
                return Err(
                    self.error("`let ... where` is a proposition binding, not an expression")
                );
            };
            let body = self.parse_contract_expression()?;
            return Ok(ContractExpression::Let {
                name: binding.name,
                c_type: binding.c_type,
                value: Box::new(value),
                body: Box::new(body),
            });
        }

        if self.peek_ident() == Some("if") {
            self.position += 1;
            let condition = self.parse_proposition()?;
            self.expect(Token::LBrace)?;
            let then_branch = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            if self.peek_ident() != Some("else") {
                return Err(self.error("expected `else` in `if` expression"));
            }
            self.position += 1;
            self.expect(Token::LBrace)?;
            let else_branch = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            return Ok(ContractExpression::If {
                condition: Box::new(condition),
                then_branch: Box::new(then_branch),
                else_branch: Box::new(else_branch),
            });
        }

        if self.peek_ident() == Some("old") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::Old(Box::new(expression)));
        }

        if self.peek_ident() == Some("at") && self.peek_next() == Some(&Token::LParen) {
            self.position += 2;
            let selector = self.parse_visit_selector()?;
            self.expect(Token::Comma)?;
            let expression = self.parse_contract_expression()?;
            self.expect(Token::RParen)?;
            return Ok(ContractExpression::At {
                selector,
                expression: Box::new(expression),
            });
        }

        if matches!(self.peek(), Some(Token::Ident(_))) && self.peek_next() == Some(&Token::LParen)
        {
            let (name, arguments) = self.parse_call_arguments("function name")?;
            return Ok(ContractExpression::Call { name, arguments });
        }

        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected contract expression, got `by`"))
            }
            Some(Token::Ident(name)) => {
                Ok(ContractExpression::CFragment(CExpression::Variable(name)))
            }
            Some(Token::Number(value)) => Ok(ContractExpression::CFragment(CExpression::Value(
                CValue::Int32(Bitvector32Term::Constant(value)),
            ))),
            Some(Token::CharLiteral(value)) => Ok(ContractExpression::CFragment(
                CExpression::Value(CValue::UInt8(Bitvector32Term::Constant(u32::from(value)))),
            )),
            Some(Token::LParen) => {
                let expression = self.parse_contract_expression()?;
                if self.peek() == Some(&Token::DotDot) {
                    self.position += 1;
                    let end = self.parse_contract_expression()?;
                    self.expect(Token::RParen)?;
                    return self.parse_range_fold(expression, end);
                }
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected contract expression, got {token:?}"))),
            None => Err(self.error("expected contract expression, got end of input")),
        }
    }

    fn parse_visit_selector(&mut self) -> Result<VisitSelector, ClickError> {
        Ok(VisitSelector::ProgramPoint(self.parse_program_point_ref()?))
    }

    fn parse_program_point_ref(&mut self) -> Result<ProgramPointRef, ClickError> {
        let region = self.parse_code_region_ref()?;
        self.expect(Token::Dot)?;
        let kind = match self.expect_ident("program point kind")?.as_str() {
            "entry" => ProgramPointKind::Entry,
            kind => {
                return Err(
                    self.error(format!("expected program point kind `entry`, got `{kind}`"))
                );
            }
        };
        Ok(ProgramPointRef { region, kind })
    }

    fn parse_range_fold(
        &mut self,
        start: ContractExpression,
        end: ContractExpression,
    ) -> Result<ContractExpression, ClickError> {
        self.expect(Token::Dot)?;
        let method = self.expect_ident("range method")?;
        if method != "fold" {
            return Err(self.error(format!(
                "unsupported range method `{method}`; expected `fold`"
            )));
        }

        self.expect(Token::LParen)?;
        let initial = self.parse_contract_expression()?;
        self.expect(Token::Comma)?;
        self.expect(Token::Pipe)?;
        let accumulator = self.expect_ident("fold accumulator name")?;
        self.expect(Token::Comma)?;
        let item = self.expect_ident("fold item name")?;
        self.expect(Token::Pipe)?;
        let body = if self.peek() == Some(&Token::LBrace) {
            self.position += 1;
            let body = self.parse_contract_expression()?;
            self.expect(Token::RBrace)?;
            body
        } else {
            self.parse_contract_expression()?
        };
        self.expect(Token::RParen)?;

        Ok(ContractExpression::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        })
    }

    fn parse_ensure_bitwise_or(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_xor()?;
        while self.peek() == Some(&Token::Pipe) {
            self.position += 1;
            let right = self.parse_ensure_bitwise_xor()?;
            expression = C0Expression::BitwiseOr(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_xor(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_bitwise_and()?;
        while self.peek() == Some(&Token::Caret) {
            self.position += 1;
            let right = self.parse_ensure_bitwise_and()?;
            expression = C0Expression::BitwiseXor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_bitwise_and(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_shift()?;
        while self.peek() == Some(&Token::Amp) {
            self.position += 1;
            let right = self.parse_ensure_shift()?;
            expression = C0Expression::BitwiseAnd(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_shift(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_add()?;
        loop {
            expression = match self.peek() {
                Some(Token::ShiftLeft) => {
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    C0Expression::ShiftLeft(Box::new(expression), Box::new(right))
                }
                Some(Token::ShiftRight) => {
                    self.position += 1;
                    let right = self.parse_ensure_add()?;
                    C0Expression::ShiftRight(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_add(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_multiply()?;
        loop {
            expression = match self.peek() {
                Some(Token::Plus) => {
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    C0Expression::Add(Box::new(expression), Box::new(right))
                }
                Some(Token::Minus) => {
                    self.position += 1;
                    let right = self.parse_ensure_multiply()?;
                    C0Expression::Subtract(Box::new(expression), Box::new(right))
                }
                _ => return Ok(expression),
            };
        }
    }

    fn parse_ensure_multiply(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_unary()?;
        loop {
            let Some(operator) = self.peek() else {
                break;
            };
            let constructor = match operator {
                Token::Star => C0Expression::Multiply,
                Token::Slash => C0Expression::Divide,
                Token::Percent => C0Expression::Remainder,
                _ => break,
            };
            self.position += 1;
            let right = self.parse_ensure_unary()?;
            expression = constructor(Box::new(expression), Box::new(right));
        }
        Ok(expression)
    }

    fn parse_ensure_unary(&mut self) -> Result<C0Expression, ClickError> {
        if self.peek() == Some(&Token::Tilde) {
            self.position += 1;
            return Ok(C0Expression::BitwiseNot(Box::new(
                self.parse_ensure_unary()?,
            )));
        }

        self.parse_ensure_postfix()
    }

    fn parse_ensure_postfix(&mut self) -> Result<C0Expression, ClickError> {
        let mut expression = self.parse_ensure_primary()?;
        loop {
            match self.peek() {
                Some(Token::LBracket) => {
                    self.position += 1;
                    let index = self.parse_ensure_expression()?;
                    self.expect(Token::RBracket)?;
                    expression = C0Expression::Index(Box::new(expression), Box::new(index));
                }
                Some(Token::Arrow) => {
                    self.position += 1;
                    let _field_name = self.expect_ident("field name")?;
                    expression = C0Expression::Load(Box::new(expression));
                }
                _ => return Ok(expression),
            }
        }
    }

    fn parse_ensure_primary(&mut self) -> Result<C0Expression, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == "by" => {
                Err(self.error("expected result expression, got `by`"))
            }
            Some(Token::Ident(name)) => Ok(C0Expression::Variable(name)),
            Some(Token::Number(value)) => Ok(C0Expression::Int32Literal(value)),
            Some(Token::CharLiteral(value)) => Ok(C0Expression::UInt8Literal(value)),
            Some(Token::LParen) => {
                let expression = self.parse_ensure_expression()?;
                self.expect(Token::RParen)?;
                Ok(expression)
            }
            Some(token) => Err(self.error(format!("expected result expression, got {token:?}"))),
            None => Err(self.error("expected result expression, got end of input")),
        }
    }

    fn expect_ident(&mut self, expected: &str) -> Result<String, ClickError> {
        match self.next() {
            Some(Token::Ident(name)) => Ok(name),
            Some(token) => Err(self.error(format!("expected {expected}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected}, got end of input"))),
        }
    }

    fn expect_ident_spelling(&mut self, expected: &str) -> Result<(), ClickError> {
        match self.next() {
            Some(Token::Ident(name)) if name == expected => Ok(()),
            Some(Token::Ident(name)) => {
                Err(self.error(format!("expected `{expected}`, got `{name}`")))
            }
            Some(token) => Err(self.error(format!("expected `{expected}`, got {token:?}"))),
            None => Err(self.error(format!("expected `{expected}`, got end of input"))),
        }
    }

    fn expect_number(&mut self, expected: &str) -> Result<u32, ClickError> {
        match self.next() {
            Some(Token::Number(value)) => Ok(value),
            Some(token) => Err(self.error(format!("expected {expected}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected}, got end of input"))),
        }
    }

    fn expect_index(&mut self, expected: &str) -> Result<usize, ClickError> {
        usize::try_from(self.expect_number(expected)?)
            .map_err(|_| self.error(format!("{expected} does not fit in usize")))
    }

    fn expect_string(&mut self, expected: &str) -> Result<String, ClickError> {
        match self.next() {
            Some(Token::String(value)) => Ok(value),
            Some(token) => Err(self.error(format!("expected {expected}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected}, got end of input"))),
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), ClickError> {
        match self.next() {
            Some(token) if token == expected => Ok(()),
            Some(token) => Err(self.error(format!("expected {expected:?}, got {token:?}"))),
            None => Err(self.error(format!("expected {expected:?}, got end of input"))),
        }
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.tokens.get(self.position).cloned()?;
        self.position += 1;
        Some(token)
    }

    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.position)
    }

    fn peek_next(&self) -> Option<&Token> {
        self.tokens.get(self.position + 1)
    }

    fn peek_ident(&self) -> Option<&str> {
        match self.peek() {
            Some(Token::Ident(name)) => Some(name),
            _ => None,
        }
    }

    fn peek_next_ident(&self) -> Option<&str> {
        match self.peek_next() {
            Some(Token::Ident(name)) => Some(name),
            _ => None,
        }
    }

    fn error(&self, message: impl Into<String>) -> ClickError {
        ClickError::new(format!("at token {}: {}", self.position, message.into()))
    }
}

fn standard_library_definitions() -> Result<
    (
        Vec<PredicateDefinition>,
        Vec<ClickFunctionDefinition>,
        Vec<ResourceDefinition>,
    ),
    ClickError,
> {
    let mut parser = Parser::new(CLICK_STANDARD_LIBRARY)?;
    let file = expand_declared_resource_clauses(parser.parse_file_items()?)?;
    if !file.verifying_sources().is_empty() || !file.function_blocks().is_empty() {
        return Err(ClickError::new(
            "internal Click standard library must not contain verifying sources or C function specs",
        ));
    }
    Ok((
        file.predicate_definitions().to_vec(),
        file.click_function_definitions().to_vec(),
        file.resource_definitions().to_vec(),
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

    Ok(file)
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
    let parameters = &resource_parameters[name];
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
    let (mut definitions, _, _) = standard_library_definitions()?;
    definitions.extend(file.predicate_definitions().iter().cloned());
    Ok(definitions)
}

fn combined_click_function_definitions(
    file: &ClickFile,
) -> Result<Vec<ClickFunctionDefinition>, ClickError> {
    let (_, mut definitions, _) = standard_library_definitions()?;
    definitions.extend(file.click_function_definitions().iter().cloned());
    Ok(definitions)
}

fn combined_resource_definitions(file: &ClickFile) -> Result<Vec<ResourceDefinition>, ClickError> {
    let (_, _, mut definitions) = standard_library_definitions()?;
    definitions.extend(file.resource_definitions().iter().cloned());
    Ok(definitions)
}

fn validate_click_definitions(file: &ClickFile) -> Result<(), ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let resource_definitions = combined_resource_definitions(file)?;

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

    for definition in &resource_definitions {
        validate_resource_definition(
            definition,
            &resources,
            &predicates,
            &click_functions,
            &click_function_types,
        )?;
    }

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

fn validate_resource_definition(
    definition: &ResourceDefinition,
    resources: &BTreeMap<String, usize>,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
) -> Result<(), ClickError> {
    let Some(representation) = definition.representation() else {
        return Ok(());
    };
    let variables = definition
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
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
    }
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

fn tokenize(source: &str) -> Result<Vec<Token>, ClickError> {
    let chars: Vec<char> = source.chars().collect();
    let mut tokens = Vec::new();
    let mut index = 0;

    while let Some(ch) = chars.get(index).copied() {
        match ch {
            ch if ch.is_whitespace() => {
                index += 1;
            }
            '{' => {
                tokens.push(Token::LBrace);
                index += 1;
            }
            '}' => {
                tokens.push(Token::RBrace);
                index += 1;
            }
            '(' => {
                tokens.push(Token::LParen);
                index += 1;
            }
            ')' => {
                tokens.push(Token::RParen);
                index += 1;
            }
            '[' => {
                tokens.push(Token::LBracket);
                index += 1;
            }
            ']' => {
                tokens.push(Token::RBracket);
                index += 1;
            }
            ':' => {
                tokens.push(Token::Colon);
                index += 1;
            }
            ',' => {
                tokens.push(Token::Comma);
                index += 1;
            }
            ';' => {
                tokens.push(Token::Semicolon);
                index += 1;
            }
            '.' => {
                if chars.get(index + 1) == Some(&'.') {
                    tokens.push(Token::DotDot);
                    index += 2;
                } else {
                    tokens.push(Token::Dot);
                    index += 1;
                }
            }
            '+' => {
                tokens.push(Token::Plus);
                index += 1;
            }
            '-' => {
                if chars.get(index + 1) == Some(&'>') {
                    tokens.push(Token::Arrow);
                    index += 2;
                } else {
                    tokens.push(Token::Minus);
                    index += 1;
                }
            }
            '*' => {
                tokens.push(Token::Star);
                index += 1;
            }
            '/' => {
                tokens.push(Token::Slash);
                index += 1;
            }
            '%' => {
                tokens.push(Token::Percent);
                index += 1;
            }
            '&' => {
                tokens.push(Token::Amp);
                index += 1;
            }
            '|' => {
                tokens.push(Token::Pipe);
                index += 1;
            }
            '^' => {
                tokens.push(Token::Caret);
                index += 1;
            }
            '~' => {
                tokens.push(Token::Tilde);
                index += 1;
            }
            '<' => {
                if chars.get(index + 1) == Some(&'<') {
                    tokens.push(Token::ShiftLeft);
                    index += 2;
                } else if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::LessEqual);
                    index += 2;
                } else {
                    tokens.push(Token::LessThan);
                    index += 1;
                }
            }
            '>' => {
                if chars.get(index + 1) == Some(&'>') {
                    tokens.push(Token::ShiftRight);
                    index += 2;
                } else if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::GreaterEqual);
                    index += 2;
                } else {
                    tokens.push(Token::GreaterThan);
                    index += 1;
                }
            }
            '!' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::BangEqual);
                    index += 2;
                } else {
                    return Err(ClickError::new(format!(
                        "expected `!=`, got `!` at byte offset {index}"
                    )));
                }
            }
            '=' => {
                if chars.get(index + 1) == Some(&'=') {
                    tokens.push(Token::EqualEqual);
                    index += 2;
                } else {
                    tokens.push(Token::Equal);
                    index += 1;
                }
            }
            '"' => {
                let (value, next_index) = tokenize_string(&chars, index)?;
                tokens.push(Token::String(value));
                index = next_index;
            }
            '\'' => {
                let (value, next_index) = tokenize_char_literal(&chars, index)?;
                tokens.push(Token::CharLiteral(value));
                index = next_index;
            }
            ch if ch.is_ascii_digit() => {
                let start = index;
                while chars.get(index).is_some_and(|next| next.is_ascii_digit()) {
                    index += 1;
                }
                let spelling: String = chars[start..index].iter().collect();
                let value = spelling.parse::<u32>().map_err(|_| {
                    ClickError::new(format!("number `{spelling}` does not fit in u32"))
                })?;
                tokens.push(Token::Number(value));
            }
            ch if is_ident_start(ch) => {
                let start = index;
                index += 1;
                while chars
                    .get(index)
                    .is_some_and(|next| is_ident_continue(*next))
                {
                    index += 1;
                }
                tokens.push(Token::Ident(chars[start..index].iter().collect()));
            }
            other => {
                return Err(ClickError::new(format!(
                    "unexpected character `{other}` at byte offset {index}"
                )));
            }
        }
    }

    Ok(tokens)
}

fn tokenize_char_literal(chars: &[char], start: usize) -> Result<(u8, usize), ClickError> {
    let Some(first) = chars.get(start + 1).copied() else {
        return Err(ClickError::new("unterminated character literal"));
    };
    let (value, end) = if first == '\\' {
        let Some(escaped) = chars.get(start + 2).copied() else {
            return Err(ClickError::new("unterminated character literal"));
        };
        let value = match escaped {
            'n' => b'\n',
            'r' => b'\r',
            't' => b'\t',
            '0' => b'\0',
            '\\' => b'\\',
            '\'' => b'\'',
            '"' => b'"',
            other => {
                return Err(ClickError::new(format!(
                    "unsupported character escape `\\{other}`"
                )));
            }
        };
        (value, start + 3)
    } else {
        if !first.is_ascii() {
            return Err(ClickError::new(
                "only ASCII character literals are supported",
            ));
        }
        (first as u8, start + 2)
    };

    if chars.get(end) != Some(&'\'') {
        return Err(ClickError::new(
            "character literals must contain exactly one byte",
        ));
    }

    Ok((value, end + 1))
}

fn tokenize_string(chars: &[char], start: usize) -> Result<(String, usize), ClickError> {
    let mut value = String::new();
    let mut index = start + 1;
    while let Some(ch) = chars.get(index).copied() {
        match ch {
            '"' => return Ok((value, index + 1)),
            '\\' => {
                let Some(escaped) = chars.get(index + 1).copied() else {
                    return Err(ClickError::new("unterminated string literal"));
                };
                match escaped {
                    '"' | '\\' => value.push(escaped),
                    'n' => value.push('\n'),
                    't' => value.push('\t'),
                    other => {
                        return Err(ClickError::new(format!(
                            "unsupported escape `\\{other}` in string literal"
                        )));
                    }
                }
                index += 2;
            }
            other => {
                value.push(other);
                index += 1;
            }
        }
    }

    Err(ClickError::new("unterminated string literal"))
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::int32;

    const FILL3_C: &str = r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                p[i] = i;
                i = i + 1;
            }
            return p[2];
        }
    "#;

    const FILL3_CLICK: &str = r#"
        verifying "fill3.c";

        int32 fill3(int32* p) {
            requires valid_range(p, 12);
            requires write(p[0..3]);
            ensures returns_second: result == 2 by auto;
        }
    "#;

    fn current(expression: CExpression) -> ContractExpression {
        ContractExpression::CFragment(expression)
    }

    fn current_var(name: &str) -> ContractExpression {
        current(CExpression::Variable(name.to_string()))
    }

    fn current_int(value: u32) -> ContractExpression {
        current(CExpression::Value(int32(value)))
    }

    fn current_index(base: &str, index: u32) -> ContractExpression {
        ContractExpression::Index(Box::new(current_var(base)), Box::new(current_int(index)))
    }

    fn old_index(base: &str, index: u32) -> ContractExpression {
        ContractExpression::Old(Box::new(current_index(base, index)))
    }

    fn ensure_comparison(
        left: ContractExpression,
        operator: ComparisonOperator,
        right: ContractExpression,
    ) -> Ensure {
        Ensure::Proposition(ClickProposition::Comparison {
            left,
            operator,
            right,
        })
    }

    #[test]
    fn parses_checked_signature_and_contract_clauses() {
        let file = parse(FILL3_CLICK).expect("sidecar should parse");

        assert_eq!(file.verifying_sources(), &["fill3.c".to_string()]);
        assert_eq!(file.function_blocks().len(), 1);
        let function = &file.function_blocks()[0];
        assert_eq!(function.signature().return_type(), C0Type::Int32);
        assert_eq!(function.signature().name(), "fill3");
        assert_eq!(
            function.signature().parameters(),
            &[FunctionParameter {
                c_type: C0Type::Int32Pointer,
                name: "p".to_string()
            }]
        );
        assert_eq!(
            function.requires(),
            &[
                Requirement::ValidRange {
                    name: "p".to_string(),
                    bytes: RangeBytes::Constant(12)
                },
                Requirement::Resource(ResourceClause::Write(ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Variable("p".to_string()),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(3)),
                }))
            ]
        );
        assert_eq!(function.ensures().len(), 1);
        let ensure = &function.ensures()[0];
        assert_eq!(ensure.name(), Some("returns_second"));
        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_var("result"),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
        assert!(ensure.proof().is_auto_tactic());
    }

    #[test]
    fn parses_symbolic_valid_range_bytes() {
        let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires valid_range(p, n * 4);
                ensures result == n by auto;
            }
        "#;
        let file = parse(source).expect("symbolic valid_range should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.requires(),
            &[Requirement::ValidRange {
                name: "p".to_string(),
                bytes: RangeBytes::Multiply(
                    Box::new(RangeBytes::Parameter("n".to_string())),
                    Box::new(RangeBytes::Constant(4)),
                )
            }]
        );
    }

    #[test]
    fn parses_valid_range_segment_syntax() {
        let source = r#"
            verifying "fill.c";

            int32 fill(int32* p, int32 n) {
                requires valid_range(p[0..n]);
                ensures result == n by auto;
            }
        "#;
        let file = parse(source).expect("segment valid_range should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.requires(),
            &[Requirement::ValidRangeSegment {
                segment: ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Variable("p".to_string()),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Variable("n".to_string()),
                },
            }]
        );
    }

    #[test]
    fn parses_valid_range_pointer_base_segment() {
        let source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range((p + 1)[0..1]);
                ensures result == 9 by auto;
            }
        "#;
        let file = parse(source).expect("pointer-base valid_range should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.requires(),
            &[Requirement::ValidRangeSegment {
                segment: ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Add(
                        Box::new(CExpression::Variable("p".to_string())),
                        Box::new(CExpression::Value(int32(1))),
                    ),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                },
            }]
        );
    }

    #[test]
    fn parses_disjoint_requirement() {
        let source = r#"
            verifying "copy.c";

            int32 copy(int32* dst, int32* src, int32 n) {
                requires disjoint(dst[0..n], src[0..n]);
                ensures result == n by auto;
            }
        "#;
        let file = parse(source).expect("disjoint requirement should parse");
        let function = &file.function_blocks()[0];

        assert!(matches!(
            function.requires()[0],
            Requirement::Disjoint { .. }
        ));
    }

    #[test]
    fn rejects_reversed_constant_valid_range_segment() {
        let c_source = r#"
            int32 read_second(int32* p) {
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "read_second.c";

            int32 read_second(int32* p) {
                requires valid_range(p[3..1]);
                ensures reads: result == p[1] by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("read_second.c", c_source)])
            .expect_err("reversed concrete segment should fail");

        assert!(
            error
                .message()
                .contains("`valid_range` segment has an end before its start"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn parses_array_parameter_signature_as_pointer() {
        let source = FILL3_CLICK.replace("int32* p", "int32 p[3]");
        let file = parse(&source).expect("array parameter signature should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.signature().parameters(),
            &[FunctionParameter {
                c_type: C0Type::Int32Pointer,
                name: "p".to_string(),
            }]
        );
    }

    #[test]
    fn parses_pilot_struct_pointer_signature_and_field_load() {
        let source = r#"
            verifying "json_object_ref_count.c";

            int32 json_object_get_ref_count(struct json_object* obj) {
                requires valid_field(obj->ref_count);
                ensures returns_ref_count: result == obj->ref_count by auto;
                immutable by frame;
            }
        "#;
        let file = parse(source).expect("pilot struct pointer signature should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(function.signature().return_type(), C0Type::Int32);
        assert_eq!(
            function.signature().parameters(),
            &[FunctionParameter {
                c_type: C0Type::Int32Pointer,
                name: "obj".to_string(),
            }]
        );
        assert_eq!(
            function.requires(),
            &[Requirement::ValidRange {
                name: "obj".to_string(),
                bytes: RangeBytes::Constant(4),
            }]
        );
        assert!(matches!(
            function.ensures()[0].ensure(),
            Ensure::Proposition(ClickProposition::Comparison { right, .. })
                if right == &ContractExpression::CFragment(
                    CExpression::Load(Box::new(CExpression::Variable("obj".to_string())))
            )
        ));
    }

    #[test]
    fn parses_pilot_struct_field_mutable_effect() {
        let source = r#"
            verifying "json_object_set_ref_count.c";

            int32 json_object_set_ref_count(struct json_object* obj, int32 count) {
                requires valid_field(obj->ref_count);
                mutable_field(obj->ref_count) by frame;
                ensures returns_count: result == count by auto;
            }
        "#;
        let file = parse(source).expect("pilot struct field effect should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(
            function.effects()[0].effect(),
            &Effect::Mutable(vec![ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("obj".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
            }])
        );
    }

    #[test]
    fn parses_block_by_clause() {
        let source = FILL3_CLICK.replace("by auto;", "by { auto; }");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(ensure.proof().is_auto_tactic());
    }

    #[test]
    fn omitted_ensure_proof_uses_default_prover() {
        let source = FILL3_CLICK.replace(" by auto", "");
        let file = parse(&source).expect("sidecar should parse omitted proof clause");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(ensure.proof().is_auto_tactic());
    }

    #[test]
    fn omitted_effect_proof_uses_default_prover() {
        let source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable;
                ensures returns_zero: result == 0;
            }
        "#;
        let file = parse(source).expect("effect proof may be omitted");
        let function = &file.function_blocks()[0];

        assert!(function.effects()[0].proof().is_auto_tactic());
        assert!(function.ensures()[0].proof().is_auto_tactic());
    }

    #[test]
    fn omitted_structural_proofs_use_default_prover() {
        let source = r#"
            verifying "count.c";

            int32 count() {
                for loop(0) {
                    invariant i >= 0;
                    mutable p[0..n];
                    step {
                        immutable;
                    }
                }

                ensures result == 3;
            }
        "#;
        let file = parse(source).expect("structural proof clauses may be omitted");
        let function = &file.function_blocks()[0];
        let items = function.structural_clauses()[0].items();

        assert!(items[0].proof().is_auto_tactic());
        assert!(items[1].proof().is_auto_tactic());
        assert!(items[2].proof().is_auto_tactic());
        assert!(function.ensures()[0].proof().is_auto_tactic());
    }

    #[test]
    fn parses_proof_step_script() {
        let source = FILL3_CLICK.replace(
            "by auto;",
            "by { symbolic_execute(); loop_vc(loop(0)); frame(loop(0)); simp(); }",
        );
        let file = parse(&source).expect("proof-step script should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.proof().steps(),
            Some(
                [
                    ProofStep::SymbolicExecute,
                    ProofStep::LoopVc(CodeRegionRef::Loop(0)),
                    ProofStep::Frame(Some(CodeRegionRef::Loop(0))),
                    ProofStep::Simp,
                ]
                .as_slice()
            )
        );
    }

    #[test]
    fn parses_represented_resource_definition() {
        let source = r#"
            affine resource uncalled(flag: int32*) {
                contains write(flag[0..1]);
                invariant flag[0] == 0;
            }
        "#;
        let file = parse(source).expect("represented resource should parse");
        let resource = &file.resource_definitions()[0];
        let representation = resource
            .representation()
            .expect("resource should have representation");

        assert_eq!(resource.name(), "uncalled");
        assert_eq!(
            resource.parameters(),
            &[FunctionParameter {
                c_type: C0Type::Int32Pointer,
                name: "flag".to_string(),
            }]
        );
        assert_eq!(
            representation.contains(),
            &[ResourceClause::Write(ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("flag".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
            })]
        );
        assert_eq!(representation.invariants().len(), 1);
    }

    #[test]
    fn parses_resource_open_and_close_steps() {
        let source = r#"
            affine resource uncalled(flag: int32*);

            verifying "identity.c";

            int32 identity(int32* flag) {
                requires uncalled(flag);

                ensures uncalled(flag) by {
                    open(uncalled(flag));
                    symbolic_execute();
                    close(uncalled(flag));
                }
            }
        "#;
        let file = parse(source).expect("resource proof steps should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.proof().steps(),
            Some(
                [
                    ProofStep::OpenResource(ResourceClause::Named {
                        name: "uncalled".to_string(),
                        arguments: vec![current_var("flag")],
                        parameter_types: vec![C0Type::Int32Pointer],
                    }),
                    ProofStep::SymbolicExecute,
                    ProofStep::CloseResource(ResourceClause::Named {
                        name: "uncalled".to_string(),
                        arguments: vec![current_var("flag")],
                        parameter_types: vec![C0Type::Int32Pointer],
                    }),
                ]
                .as_slice()
            )
        );
    }

    #[test]
    fn parses_bounded_execute_proof_step() {
        let source = FILL3_CLICK.replace("by auto;", "by { bounded_execute(); }");
        let file = parse(&source).expect("bounded proof-step script should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.proof().steps(),
            Some([ProofStep::BoundedExecute].as_slice())
        );
    }

    #[test]
    fn parses_unfold_proof_step() {
        let source = FILL3_CLICK.replace(
            "by auto;",
            "by { symbolic_execute(); unfold(sorted); simp(); }",
        );
        let file = parse(&source).expect("unfold proof-step script should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.proof().steps(),
            Some(
                [
                    ProofStep::SymbolicExecute,
                    ProofStep::Unfold("sorted".to_string()),
                    ProofStep::Simp,
                ]
                .as_slice()
            )
        );
    }

    #[test]
    fn parses_existential_proof_steps() {
        let source = FILL3_CLICK.replace(
            "by auto;",
            "by { symbolic_execute(); choose(k from requirement has_k); witness(j = k + 1); simp(); }",
        );
        let file = parse(&source).expect("existential proof-step script should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.proof().steps(),
            Some(
                [
                    ProofStep::SymbolicExecute,
                    ProofStep::Choose(ProofChoice {
                        name: "k".to_string(),
                        source: ProofFactSource::RequirementLabel("has_k".to_string()),
                    }),
                    ProofStep::Witness(ProofWitness {
                        name: "j".to_string(),
                        value: ContractExpression::Add(
                            Box::new(current_var("k")),
                            Box::new(current_int(1)),
                        ),
                    }),
                    ProofStep::Simp,
                ]
                .as_slice()
            )
        );
    }

    #[test]
    fn parses_labeled_requirement() {
        let source = r#"
            verifying "id.c";

            int32 id(int32 x) {
                requires has_x: exists (int32 k) { k == x };
                ensures result == x by auto;
            }
        "#;
        let file = parse(source).expect("labeled requirement should parse");
        let requirement = &file.function_blocks()[0].requires()[0];

        assert_eq!(requirement.label(), Some("has_x"));
        assert!(matches!(
            requirement.inner(),
            Requirement::Proposition(ClickProposition::Exists { .. })
        ));
    }

    #[test]
    fn parses_unnamed_ensure_clause() {
        let source =
            FILL3_CLICK.replace("ensures returns_second: result == 2", "ensures result == 2");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(ensure.name(), None);
        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_var("result"),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
    }

    #[test]
    fn parses_simp_tactic() {
        let source = FILL3_CLICK.replace("by auto", "by simp");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(matches!(ensure.proof().tactic(), Some(Tactic::Simp)));
    }

    #[test]
    fn parses_frame_tactic() {
        let source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                mutable p[1..2] by frame;
                ensures returns_written: result == 9 by auto;
            }
        "#;
        let file = parse(source).expect("frame tactic should parse");
        let effect = &file.function_blocks()[0].effects()[0];

        assert!(matches!(effect.proof().tactic(), Some(Tactic::Frame)));
    }

    #[test]
    fn parses_memory_postcondition() {
        let source = FILL3_CLICK.replace("result == 2", "p[2] == 2");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_index("p", 2),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
    }

    #[test]
    fn parses_old_memory_postcondition() {
        let source = FILL3_CLICK.replace("result == 2", "p[0] == old(p[0])");
        let file = parse(&source).expect("sidecar should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert_eq!(
            ensure.ensure(),
            &ensure_comparison(
                current_index("p", 0),
                ComparisonOperator::Equal,
                old_index("p", 0),
            )
        );
    }

    #[test]
    fn parses_loop_invariants_and_statement_asserts() {
        let source = r#"
            verifying "count.c";

            int32 count() {
                for statement(2) as initialized {
                    assert i == 0 by auto;
                }

                for loop(0) as count_loop {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                    mutable p[0..n] by auto;
                    step {
                        immutable by auto;
                    }
                }

                ensures result == 3 by auto;
            }
        "#;
        let file = parse(source).expect("sidecar should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(function.structural_clauses().len(), 2);
        assert_eq!(
            function.structural_clauses()[0].region(),
            &CodeRegion::Statement(2)
        );
        assert_eq!(
            function.structural_clauses()[0].label(),
            Some("initialized")
        );
        assert_eq!(
            function.structural_clauses()[0].items()[0].kind(),
            StructuralItemKind::Assert
        );
        assert_eq!(
            function.structural_clauses()[1].region(),
            &CodeRegion::Loop(0)
        );
        assert_eq!(function.structural_clauses()[1].label(), Some("count_loop"));
        assert_eq!(function.structural_clauses()[1].items().len(), 4);
        assert_eq!(
            function.structural_clauses()[1].items()[0].kind(),
            StructuralItemKind::Invariant
        );
        assert_eq!(
            function.structural_clauses()[1].items()[2].kind(),
            StructuralItemKind::Effect
        );
        assert!(matches!(
            function.structural_clauses()[1].items()[2].effect(),
            Some(Effect::Mutable(_))
        ));
        assert!(matches!(
            function.structural_clauses()[1].items()[3].effect(),
            Some(Effect::Immutable)
        ));
        assert_eq!(
            function.structural_clauses()[1].items()[3].kind(),
            StructuralItemKind::StepEffect
        );
    }

    #[test]
    fn rejects_legacy_structural_region_syntax() {
        let source = r#"
            verifying "count.c";

            int32 count() {
                loop 0 {
                    invariant i >= 0 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;
        let error = parse(source).expect_err("legacy loop block syntax should fail");

        assert!(
            error.message().contains("expected `let`, `requires`"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn rejects_legacy_proof_step_region_syntax() {
        let source = FILL3_CLICK.replace("by auto;", "by { symbolic_execute(); loop_vc(loop 0); }");
        let error = parse(&source).expect_err("legacy proof-step region syntax should fail");

        assert!(
            error.message().contains("expected LParen"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn parses_click_proposition_syntax() {
        let source = r#"
            verifying "logic.c";

            predicate nonnegative(int32 x) {
                x >= 0
            }

            int32 logic(int32 x) {
                requires x >= 0 and x < 10;
                requires nonnegative(x);
                ensures bounded: result >= 0 and result < 10 by auto;
                ensures implication: result == x implies result >= 0 by auto;
                ensures named_predicate: nonnegative(result) by auto;
                ensures quantified: forall (int32 k) {
                    0 <= k implies k >= 0
                } by auto;
                immutable by auto;
                mutable p[0..n], q[1..m] by auto;
            }
        "#;
        let file = parse(source).expect("proposition syntax should parse");
        let function = &file.function_blocks()[0];

        assert_eq!(file.predicate_definitions().len(), 1);
        assert_eq!(file.predicate_definitions()[0].name(), "nonnegative");
        assert!(matches!(
            function.requires()[0],
            Requirement::Proposition(ClickProposition::And(_, _))
        ));
        assert!(matches!(
            function.requires()[1],
            Requirement::Proposition(ClickProposition::PredicateCall { .. })
        ));
        assert!(matches!(
            function.ensures()[0].ensure(),
            Ensure::Proposition(ClickProposition::And(_, _))
        ));
        assert!(matches!(
            function.ensures()[1].ensure(),
            Ensure::Proposition(ClickProposition::Implies(_, _))
        ));
        assert!(matches!(
            function.ensures()[2].ensure(),
            Ensure::Proposition(ClickProposition::PredicateCall { .. })
        ));
        assert!(matches!(
            function.ensures()[3].ensure(),
            Ensure::Proposition(ClickProposition::ForAll { .. })
        ));
        assert_eq!(function.effects().len(), 2);
        assert!(matches!(function.effects()[0].effect(), Effect::Immutable));
        match function.effects()[1].effect() {
            Effect::Mutable(segments) => assert_eq!(segments.len(), 2),
            effect => panic!("expected mutable effect, got {effect:?}"),
        }
    }

    #[test]
    fn parses_rust_style_let_annotations() {
        let source = r#"
            function inc_with_let(int32 x) -> int32 {
                let next: int32 = x + 1;
                next
            }
        "#;
        let file = parse(source).expect("Rust-style let annotation should parse");
        let body = file.click_function_definitions()[0].body();

        assert!(matches!(
            body,
            ContractExpression::Let {
                name,
                c_type: Some(C0Type::Int32),
                ..
            } if name == "next"
        ));
    }

    #[test]
    fn parses_contract_level_let_bindings() {
        let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                let expected: int32 = x;

                ensures result_value: result == expected by auto;
            }
        "#;
        let file = parse(source).expect("contract-level let should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(matches!(
            ensure.ensure(),
            Ensure::Proposition(ClickProposition::Comparison {
                right: ContractExpression::Let {
                    name,
                    c_type: Some(C0Type::Int32),
                    ..
                },
                ..
            }) if name == "expected"
        ));
    }

    #[test]
    fn parses_contract_level_let_where_bindings() {
        let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                let k: int32 where k == x;

                ensures result_value: result == k by auto;
            }
        "#;
        let file = parse(source).expect("contract-level let-where should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(matches!(
            ensure.ensure(),
            Ensure::Proposition(ClickProposition::Exists {
                c_type: C0Type::Int32,
                name,
                body,
            }) if name == "k"
                && matches!(body.as_ref(), ClickProposition::And(_, _))
        ));
    }

    #[test]
    fn parses_proposition_let_where_bindings() {
        let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result_value:
                    let k: int32 where k == x;
                    result == k
                    by auto;
            }
        "#;
        let file = parse(source).expect("proposition let-where should parse");
        let ensure = &file.function_blocks()[0].ensures()[0];

        assert!(matches!(
            ensure.ensure(),
            Ensure::Proposition(ClickProposition::Exists {
                c_type: C0Type::Int32,
                name,
                ..
            }) if name == "k"
        ));
    }

    #[test]
    fn rejects_contract_let_parameter_name_conflict() {
        let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                let x = 0;

                ensures result_value: result == x by auto;
            }
        "#;
        let error = parse(source).expect_err("contract let should not reuse parameter name");

        assert!(
            error
                .message()
                .contains("contract `let` `x` conflicts with a C parameter")
        );
    }

    #[test]
    fn rejects_unknown_predicate_call() {
        let source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures unknown(x) by auto;
            }
        "#;

        let error = parse(source).expect_err("unknown predicate should fail");

        assert!(
            error.message().contains("unknown predicate `unknown`"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn rejects_predicate_call_with_wrong_arity() {
        let source = r#"
            verifying "identity.c";

            predicate nonnegative(int32 x) {
                x >= 0
            }

            int32 identity(int32 x) {
                ensures nonnegative(x, x) by auto;
            }
        "#;

        let error = parse(source).expect_err("wrong predicate arity should fail");

        assert!(
            error
                .message()
                .contains("predicate `nonnegative` expects 1 argument(s), got 2"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_opaque_predicate_from_requirement() {
        let c_source = r#"
            int32 identity_pointer_fact(int32* p) {
                return 0;
            }
        "#;
        let click_source = r#"
            verifying "identity_pointer_fact.c";

            predicate sorted_pair(int32* p) {
                p[0] <= p[1]
            }

            int32 identity_pointer_fact(int32* p) {
                requires sorted_pair(p);
                ensures still_sorted: sorted_pair(p) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity_pointer_fact.c", c_source)])
            .expect("exact opaque predicate fact should verify");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn unfolds_predicate_requirement_to_prove_consequence() {
        let c_source = r#"
            int32 keep_pair(int32* p) {
                return 0;
            }
        "#;
        let click_source = r#"
            verifying "keep_pair.c";

            predicate sorted_pair(int32* p) {
                p[0] <= p[1]
            }

            int32 keep_pair(int32* p) {
                requires valid_range(p, 8);
                requires sorted_pair(p);
                ensures consequence: p[0] <= p[1] by {
                    symbolic_execute();
                    unfold(sorted_pair);
                    simp();
                }
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("keep_pair.c", c_source)])
            .expect("unfolded predicate requirement should prove its body");

        assert_eq!(verified.len(), 1);
        assert_eq!(
            verified[0].proof_steps(),
            Some(
                [
                    ProofStep::SymbolicExecute,
                    ProofStep::Unfold("sorted_pair".to_string()),
                    ProofStep::Simp,
                ]
                .as_slice()
            )
        );
    }

    #[test]
    fn unfolds_predicate_goal_to_prove_compare_swap_sorted() {
        let c_source = r#"
            int32 compare_swap2(int32* p) {
                int32 tmp;
                if (p[1] < p[0]) {
                    tmp = p[0];
                    p[0] = p[1];
                    p[1] = tmp;
                } else {
                    tmp = 0;
                }
                return 0;
            }
        "#;
        let click_source = r#"
            verifying "compare_swap2.c";

            predicate sorted_pair(int32* p) {
                p[0] <= p[1]
            }

            int32 compare_swap2(int32* p) {
                requires valid_range(p, 8);
                requires write(p[0..2]);
                ensures sorted: sorted_pair(p) by {
                    symbolic_execute();
                    unfold(sorted_pair);
                    simp();
                }
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("compare_swap2.c", c_source)])
            .expect("unfolded predicate goal should prove compare-swap sortedness");

        assert_eq!(verified.len(), 2);
    }

    #[test]
    fn unfolds_general_sorted_predicate() {
        let c_source = r#"
            int32 keep_sorted(int32* p, int32 n) {
                return 0;
            }
        "#;
        let click_source = r#"
            verifying "keep_sorted.c";

            predicate sorted(int32* p, int32 n) {
                forall (int32 i) {
                    forall (int32 j) {
                        0 <= i and 0 <= j and i < j and j < n implies p[i] <= p[j]
                    }
                }
            }

            int32 keep_sorted(int32* p, int32 n) {
                requires n >= 0;
                requires valid_range(p[0..n]);
                requires sorted(p, n);
                ensures still_sorted: sorted(p, n) by {
                    symbolic_execute();
                    unfold(sorted);
                    simp();
                }
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("keep_sorted.c", c_source)])
            .expect("general sorted predicate should unfold deterministically");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn verifies_click_proposition_logic() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures prop_logic: result == x and not (result != x) by auto;
                ensures prop_implies: result == x implies result == x by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect("proposition logic should verify");

        assert_eq!(verified.len(), 2);
    }

    #[test]
    fn verifies_simp_normalizes_simple_postconditions() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures add_zero: result == x + 0 by simp;
                ensures prop_simp: result == x and not (result != x) by simp;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect("simp should prove local normalized postconditions");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::Simp);
        assert_eq!(verified[1].proof_kind(), ProofKind::Simp);
    }

    #[test]
    fn verifies_simple_postcondition_with_proof_steps() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x by {
                    symbolic_execute();
                    simp();
                }
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect("proof-step script should prove simple postcondition");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::ProofSteps);
    }

    #[test]
    fn verifies_omitted_proof_with_default_prover() {
        let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
        let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable;
                ensures returns_zero: result == 0;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("zero.c", c_source)])
            .expect("omitted proof clauses should use the default prover");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
        assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_mutable_effect_with_bounded_frame_steps() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                mutable p[1..2] by {
                    bounded_execute();
                    frame();
                }
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("bounded frame proof steps should prove mutable effect");
        let expected_steps = [ProofStep::BoundedExecute, ProofStep::Frame(None)];

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::ProofSteps);
        assert_eq!(verified[0].proof_steps(), Some(expected_steps.as_slice()));
    }

    #[test]
    fn bare_frame_step_rejects_ensure_claim() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_x: result == x by {
                    symbolic_execute();
                    frame();
                }
            }
        "#;

        let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect_err("bare frame step should not prove postconditions");

        assert!(
            error
                .message()
                .contains("`frame()` proves function-level effect claims"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn auto_certificate_replays_for_bounded_execution() {
        let c_source = r#"
            int32 fill3_array_loop(int32 p[3]) {
                int32 i;
                i = 0;
                while (i < 3) {
                    p[i] = i;
                    i = i + 1;
                }
                return p[2];
            }
        "#;
        let auto_click_source = r#"
            verifying "fill3_array_loop.c";

            int32 fill3_array_loop(int32 p[3]) {
                requires valid_range(p, 12);
                requires write(p[0..3]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }
                ensures writes_third: p[2] == 2 by auto;
            }
        "#;

        let auto_verified =
            verify_c0_sources(auto_click_source, &[("fill3_array_loop.c", c_source)])
                .expect("bounded auto proof should verify");
        let expected_steps = [ProofStep::BoundedExecute, ProofStep::Simp];

        assert_eq!(auto_verified.len(), 1);
        assert_eq!(auto_verified[0].proof_kind(), ProofKind::BoundedExecution);
        assert_eq!(
            auto_verified[0].proof_steps(),
            Some(expected_steps.as_slice())
        );

        let explicit_click_source = r#"
            verifying "fill3_array_loop.c";

            int32 fill3_array_loop(int32 p[3]) {
                requires valid_range(p, 12);
                requires write(p[0..3]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }
                ensures writes_third: p[2] == 2 by {
                    bounded_execute();
                    simp();
                }
            }
        "#;

        let explicit_verified =
            verify_c0_sources(explicit_click_source, &[("fill3_array_loop.c", c_source)])
                .expect("bounded auto certificate should replay as explicit proof steps");

        assert_eq!(explicit_verified.len(), 1);
        assert_eq!(explicit_verified[0].proof_kind(), ProofKind::ProofSteps);
        assert_eq!(
            explicit_verified[0].proof_steps(),
            Some(expected_steps.as_slice())
        );
    }

    #[test]
    fn simp_rejects_effect_clauses() {
        let c_source = r#"
            int32 zero() {
                return 0;
            }
        "#;
        let click_source = r#"
            verifying "zero.c";

            int32 zero() {
                immutable by simp;
                ensures returns_zero: result == 0 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("zero.c", c_source)])
            .expect_err("simp should not prove effect clauses");

        assert!(
            error
                .message()
                .contains("`simp` does not prove effect clauses"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn simp_rejects_loop_backed_claims() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                ensures returns_three: result == 3 by simp;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("simp should not run loop verification");

        assert!(
            error
                .message()
                .contains("`simp` does not prove loop-backed claims"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_symbolic_result_expression() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_argument: result == x by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect("identity sidecar should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(
            verified[0].ensure_clause().unwrap().ensure(),
            &ensure_comparison(
                current_var("result"),
                ComparisonOperator::Equal,
                current_var("x"),
            )
        );
    }

    #[test]
    fn verifies_memory_postcondition() {
        let source = FILL3_CLICK.replace(
            "ensures returns_second: result == 2",
            "ensures third: p[2] == 2",
        );
        let verified = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect("fill3 memory postcondition should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(
            verified[0].ensure_clause().unwrap().ensure(),
            &ensure_comparison(
                current_index("p", 2),
                ComparisonOperator::Equal,
                current_int(2),
            )
        );
    }

    #[test]
    fn verifies_old_memory_postcondition_for_unmodified_cell() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                ensures writes_second: p[1] == 9 by auto;
                ensures keeps_first: p[0] == old(p[0]) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("old memory postcondition should verify");

        assert_eq!(verified.len(), 2);
        assert_eq!(
            verified[1].ensure_clause().unwrap().ensure(),
            &ensure_comparison(
                current_index("p", 0),
                ComparisonOperator::Equal,
                old_index("p", 0),
            )
        );
    }

    #[test]
    fn verifies_quantified_old_memory_postcondition() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                ensures keeps_first_cell: forall (int32 k) {
                    0 <= k and k < 1 implies p[k] == old(p[k])
                } by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("unwritten segment should match old memory");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn disjoint_requirement_proves_symbolic_unwritten_read() {
        let c_source = r#"
            int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
                p[i] = 9;
                return p[j];
            }
        "#;
        let click_source = r#"
            verifying "write_i_read_j.c";

            int32 write_i_read_j(int32 p[], int32 i, int32 j, int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires i >= 0;
                requires i < n;
                requires j >= 0;
                requires j < n;
                requires valid_range(p[0..n]);
                requires write(p[i..i + 1]);
                requires read(p[j..j + 1]);
                requires disjoint(p[i..i + 1], p[j..j + 1]);
                mutable p[i..i + 1] by frame;
                ensures keeps_j: result == old(p[j]) by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_i_read_j.c", c_source)])
            .expect("disjoint singleton ranges should prove symbolic unwritten read");

        assert_eq!(verified.len(), 2);
    }

    #[test]
    fn quantified_old_memory_rejects_overwritten_cell() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                ensures keeps_second_cell: forall (int32 k) {
                    1 <= k and k < 2 implies p[k] == old(p[k])
                } by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("overwritten segment should not match old memory");

        assert!(
            error.message().contains("proposition was not provable"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_mutable_segment_effect() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                mutable p[1..2] by frame;
                mutable p[0..2] by frame;
                ensures returns_written: result == 9 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("write should stay inside declared segments");

        assert_eq!(verified.len(), 3);
        assert!(matches!(
            verified[0].effect_clause().unwrap().effect(),
            Effect::Mutable(_)
        ));
        assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
        assert_eq!(verified[1].proof_kind(), ProofKind::Frame);
    }

    #[test]
    fn verifies_shifted_valid_range_and_mutable_segment() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range((p + 1)[0..1]);
                requires write((p + 1)[0..1]);
                mutable (p + 1)[0..1] by frame;
                ensures returns_written: result == 9 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect("shifted valid_range should prove access and frame");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
        assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn frame_rejects_ensure_clause() {
        let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
        let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures returns_argument: result == x by frame;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("identity.c", c_source)])
            .expect_err("frame should not prove postconditions");

        assert!(
            error
                .message()
                .contains("`frame` only proves effect clauses"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn mutable_segment_rejects_write_outside_segment() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                mutable p[0..1] by auto;
                ensures returns_written: result == 9 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("write outside segment should fail");

        assert!(
            error.message().contains("outside the mutable footprint"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("write to `p[1]`"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("mutable segments: [p[0..1]]"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("evaluated segments"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn immutable_rejects_external_memory_write() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                immutable by auto;
                ensures returns_written: result == 9 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("immutable should reject external memory writes");

        assert!(
            error.message().contains("outside the mutable footprint"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("evaluated segments"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn immutable_allows_stack_local_writes() {
        let c_source = r#"
            int32 count_to_one() {
                int32 i;
                i = 0;
                i = i + 1;
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_one.c";

            int32 count_to_one() {
                immutable by frame;
                ensures returns_one: result == 1 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("count_to_one.c", c_source)])
            .expect("stack-local writes should not count as external mutation");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
    }

    #[test]
    fn old_memory_postcondition_fails_for_overwritten_cell() {
        let c_source = r#"
            int32 write_second(int32* p) {
                p[1] = 9;
                return p[1];
            }
        "#;
        let click_source = r#"
            verifying "write_second.c";

            int32 write_second(int32* p) {
                requires valid_range(p, 8);
                requires write(p[1..2]);
                ensures keeps_second: p[1] == old(p[1]) by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("write_second.c", c_source)])
            .expect_err("old memory postcondition for overwritten cell should fail");

        assert!(
            error
                .message()
                .contains("left side evaluated to 9, right side evaluated to load(p[1])"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_loop_invariants_and_statement_assert() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                for statement(2) {
                    assert i == 0 by auto;
                }

                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect("loop invariants and statement assert should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_old_memory_loop_invariant() {
        let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
                int32 i;
                i = 1;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1 and n <= 2147483647;
                requires valid_range(p, n * 4);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 1 and i <= n by auto;
                    invariant p[0] == old(p[0]) by auto;
                }
                ensures frame_and_result: p[0] == old(p[0]) and result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
            .expect("old memory loop invariant should verify");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn verifies_old_memory_loop_invariant_with_segment_bounds() {
        let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
                int32 i;
                i = 1;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1 and n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 1 and i <= n by auto;
                    invariant forall (int32 k) {
                        0 <= k and k < 1 implies p[k] == old(p[k])
                    } by auto;
                }
                ensures frame_and_result: forall (int32 k) {
                    0 <= k and k < 1 implies p[k] == old(p[k])
                } and result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
            .expect("old memory segment loop invariant should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_symbolic_segment_valid_range() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("segment valid_range should verify symbolic pointer loop");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_symbolic_loop_mutable_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                }
                mutable p[0..n] by auto;
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("symbolic pointer loop writes should stay inside segment");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_loop_level_mutable_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[0..n] by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("loop-level mutable segment should verify each iteration");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_loop_level_iteration_relative_mutable_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    step {
                        mutable p[i..i + 1] by frame;
                    }
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("loop-level mutable segment should support one-cell iteration ranges");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn loop_whole_mutable_rejects_loop_modified_local_in_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[i..i + 1] by frame;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect_err("whole-loop mutable footprint should reject loop-modified locals");

        assert!(
            error.message().contains("whole-loop `mutable` segment"),
            "{}",
            error.message()
        );
        assert!(error.message().contains("`i`"), "{}", error.message());
        assert!(error.message().contains("step"), "{}", error.message());
    }

    #[test]
    fn verifies_loop_level_growing_prefix_mutable_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    step {
                        mutable p[0..i + 1] by frame;
                    }
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("loop-level frame should support growing prefix segments");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_loop_level_shifted_suffix_mutable_segment() {
        let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
                int32 i;
                i = 1;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 1 by auto;
                    invariant i <= n by auto;
                    mutable p[1..n] by frame;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
            .expect("loop-level frame should support shifted suffix segments");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn verifies_loop_level_multi_segment_mutable_footprint() {
        let c_source = r#"
            int32 fill_two(int32 p[], int32 q[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    q[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_two.c";

            int32 fill_two(int32 p[], int32 q[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires valid_range(q[0..n]);
                requires write(p[0..n]);
                requires write(q[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    step {
                        mutable p[i..i + 1], q[i..i + 1] by frame;
                    }
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_two.c", c_source)])
            .expect("loop-level frame should support multiple mutable segments");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn loop_level_mutable_segment_rejects_write_outside_segment() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[0..0] by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect_err("write outside loop mutable segment should fail");

        assert!(
            error.message().contains("loop 0 mutable 0"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("outside the mutable footprint"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("evaluated segments"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("external writes"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("declared effect"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn loop_level_immutable_rejects_external_memory_write() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    immutable by auto;
                }
                ensures returns_n: result == n by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect_err("loop-level immutable should reject external writes");

        assert!(
            error.message().contains("loop 0 immutable 0"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("outside the mutable footprint"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn loop_level_immutable_allows_stack_local_update() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= 3 by auto;
                    immutable by frame;
                }
                ensures returns_three: result == 3 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect("loop-level immutable should allow stack-local updates");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn function_immutable_allows_nonwriting_loop_with_mutable_bound() {
        let c_source = r#"
            int32 count_pointer_bound(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_pointer_bound.c";

            int32 count_pointer_bound(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[0..n] by frame;
                }
                immutable by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("count_pointer_bound.c", c_source)])
            .expect("a mutable upper bound does not imply the loop actually writes memory");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
        assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn function_mutable_uses_loop_effect_summary() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[0..n] by frame;
                }
                mutable p[0..n] by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect("function-level mutable should consume loop effect summary");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
        assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn function_mutable_rejects_loop_effect_outside_function_bound() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[0..n] by frame;
                }
                mutable p[0..0] by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect_err("function-level mutable should reject a wider loop effect summary");

        assert!(
            error.message().contains("effect summary range"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("outside the mutable footprint"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn function_mutable_accepts_shifted_loop_effect_subset() {
        let c_source = r#"
            int32 fill_tail(int32 p[], int32 n) {
                int32 i;
                i = 1;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_tail.c";

            int32 fill_tail(int32 p[], int32 n) {
                requires n >= 1;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 1 by auto;
                    invariant i <= n by auto;
                    mutable (p + 1)[0..n - 1] by frame;
                }
                mutable p[0..n] by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("fill_tail.c", c_source)])
            .expect("function-level mutable should accept a shifted loop effect subset");

        assert_eq!(verified.len(), 2);
        assert_eq!(verified[0].proof_kind(), ProofKind::Frame);
        assert_eq!(verified[1].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn function_immutable_rejects_writing_loop_effect_summary() {
        let c_source = r#"
            int32 fill_n(int32 p[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    p[i] = i;
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "fill_n.c";

            int32 fill_n(int32 p[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(p[0..n]);
                requires write(p[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    mutable p[0..n] by frame;
                }
                immutable by frame;
                ensures returns_n: result == n by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("fill_n.c", c_source)])
            .expect_err("function-level immutable should reject a writing loop effect summary");

        assert!(
            error.message().contains("effect summary range"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn structural_invariant_rejects_frame_tactic() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                for loop(0) {
                    invariant i >= 0 by frame;
                }
                ensures returns_three: result == 3 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("frame should not prove invariants");

        assert!(
            error
                .message()
                .contains("`invariant` structural clauses must use"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn structural_invariant_allows_unfold_only_steps() {
        let c_source = r#"
            int32 loop_sorted_range_invariant(int32 p[3]) {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "loop_sorted_range_invariant.c";

            predicate sorted(int32 p[], int32 n) {
                sorted_range(p, 0, n)
            }

            predicate sorted_range(int32 p[], int32 lo, int32 hi) {
                forall (int32 i) {
                    forall (int32 j) {
                        0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
                    }
                }
            }

            int32 loop_sorted_range_invariant(int32 p[3]) {
                requires valid_range(p[0..3]);
                requires sorted(p, 3);
                for loop(0) {
                    invariant i >= 0 and i <= 3 by auto;
                    invariant sorted(p, 3) by {
                        unfold(sorted);
                        unfold(sorted_range);
                    }
                    immutable by frame;
                }
                ensures still_sorted: sorted(p, 3) by {
                    symbolic_execute();
                    loop_vc(loop(0));
                    frame(loop(0));
                    unfold(sorted);
                    unfold(sorted_range);
                    simp();
                }
            }
        "#;

        let verified =
            verify_c0_sources(click_source, &[("loop_sorted_range_invariant.c", c_source)])
                .expect("unfold-only structural invariant script should verify");

        assert_eq!(verified.len(), 1);
    }

    #[test]
    fn verifies_symbolic_copy_segment_invariant() {
        let c_source = r#"
            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    dst[i] = src[i];
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "copy_n.c";

            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(dst[0..n]);
                requires valid_range(src[0..n]);
                requires write(dst[0..n]);
                requires read(src[0..n]);
                requires disjoint(dst[0..n], src[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    invariant forall (int32 k) {
                        0 <= k and k < i implies dst[k] == old(src[k])
                    } by auto;
                    mutable dst[0..n] by auto;
                }
                ensures returns_n: result == n by auto;
                ensures source_unchanged: forall (int32 k) {
                    0 <= k and k < n implies src[k] == old(src[k])
                } by {
                    symbolic_execute();
                    loop_vc(loop(0));
                    frame(loop(0));
                    simp();
                }
                ensures copied_segment: forall (int32 k) {
                    0 <= k and k < n implies dst[k] == old(src[k])
                } by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("copy_n.c", c_source)])
            .expect("symbolic copy loop should prove copied segment invariant");

        assert_eq!(verified.len(), 3);
        assert_eq!(verified[0].proof_kind(), ProofKind::LoopVerification);
    }

    #[test]
    fn auto_certificate_replays_for_loop_frame_claim() {
        let c_source = r#"
            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                int32 i;
                i = 0;
                while (i < n) {
                    dst[i] = src[i];
                    i = i + 1;
                }
                return i;
            }
        "#;
        let auto_click_source = r#"
            verifying "copy_n.c";

            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(dst[0..n]);
                requires valid_range(src[0..n]);
                requires write(dst[0..n]);
                requires read(src[0..n]);
                requires disjoint(dst[0..n], src[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    invariant forall (int32 k) {
                        0 <= k and k < i implies dst[k] == old(src[k])
                    } by auto;
                    mutable dst[0..n] by auto;
                }
                ensures source_unchanged: forall (int32 k) {
                    0 <= k and k < n implies src[k] == old(src[k])
                } by auto;
            }
        "#;

        let auto_verified = verify_c0_sources(auto_click_source, &[("copy_n.c", c_source)])
            .expect("auto should prove the source-memory postcondition");
        let source_unchanged = auto_verified
            .iter()
            .find(|theorem| {
                theorem
                    .ensure_clause()
                    .and_then(EnsureClause::name)
                    .is_some_and(|name| name == "source_unchanged")
            })
            .expect("source_unchanged theorem should be present");
        let expected_steps = [
            ProofStep::SymbolicExecute,
            ProofStep::LoopVc(CodeRegionRef::Loop(0)),
            ProofStep::Frame(Some(CodeRegionRef::Loop(0))),
            ProofStep::Simp,
        ];

        assert_eq!(source_unchanged.proof_kind(), ProofKind::LoopVerification);
        assert_eq!(
            source_unchanged.proof_steps(),
            Some(expected_steps.as_slice())
        );

        let explicit_click_source = r#"
            verifying "copy_n.c";

            int32 copy_n(int32 dst[], int32 src[], int32 n) {
                requires n >= 0;
                requires n <= 2147483647;
                requires valid_range(dst[0..n]);
                requires valid_range(src[0..n]);
                requires write(dst[0..n]);
                requires read(src[0..n]);
                requires disjoint(dst[0..n], src[0..n]);
                for loop(0) {
                    invariant i >= 0 by auto;
                    invariant i <= n by auto;
                    invariant forall (int32 k) {
                        0 <= k and k < i implies dst[k] == old(src[k])
                    } by auto;
                    mutable dst[0..n] by auto;
                }
                ensures source_unchanged: forall (int32 k) {
                    0 <= k and k < n implies src[k] == old(src[k])
                } by {
                    symbolic_execute();
                    loop_vc(loop(0));
                    frame(loop(0));
                    simp();
                }
            }
        "#;

        let explicit_verified = verify_c0_sources(explicit_click_source, &[("copy_n.c", c_source)])
            .expect("auto certificate should replay as explicit proof steps");

        assert_eq!(explicit_verified.len(), 1);
        assert_eq!(explicit_verified[0].proof_kind(), ProofKind::ProofSteps);
        assert_eq!(
            explicit_verified[0].proof_steps(),
            Some(expected_steps.as_slice())
        );
    }

    #[test]
    fn false_loop_invariant_fails() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                for loop(0) {
                    invariant i < 3 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("false loop invariant should fail");

        assert!(
            error.message().contains("loop 0 invariant 0 preservation"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn false_loop_invariant_initialization_fails() {
        let c_source = r#"
            int32 count_to_three() {
                int32 i;
                i = 0;
                while (i < 3) {
                    i = i + 1;
                }
                return i;
            }
        "#;
        let click_source = r#"
            verifying "count_to_three.c";

            int32 count_to_three() {
                for loop(0) {
                    invariant i == 1 by auto;
                }

                ensures result == 3 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("count_to_three.c", c_source)])
            .expect_err("false loop invariant initialization should fail");

        assert!(
            error.message().contains("loop 0 invariant 0 entry"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_symbolic_increment_with_numeric_requirement() {
        let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
        let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                requires x < 2147483647;
                ensures increments: result == x + 1 by auto;
            }
        "#;

        let verified = verify_c0_sources(click_source, &[("increment.c", c_source)])
            .expect("increment sidecar should verify");

        assert_eq!(verified.len(), 1);
        assert_eq!(verified[0].specification.requires().len(), 1);
    }

    #[test]
    fn symbolic_increment_without_numeric_requirement_fails() {
        let c_source = r#"
            int32 increment(int32 x) {
                return x + 1;
            }
        "#;
        let click_source = r#"
            verifying "increment.c";

            int32 increment(int32 x) {
                ensures increments: result == x + 1 by auto;
            }
        "#;

        let error = verify_c0_sources(click_source, &[("increment.c", c_source)])
            .expect_err("increment without overflow requirement should fail");

        assert!(
            error
                .message()
                .contains("failed for `increment.increments` path"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn verifies_fill3_c0_source_with_sidecar_specification() {
        let verified = verify_c0_sources(FILL3_CLICK, &[("fill3.c", FILL3_C)])
            .expect("fill3 sidecar should verify");

        assert_eq!(verified.len(), 1);
        let verified = &verified[0];
        let base = Pointer {
            block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.to_string(),
            offset: scale_int32_offset(
                Bitvector32Term::Variable(Variable(POINTER_ARGUMENT_VARIABLE_BASE)),
                4,
            ),
        };
        let first = base.clone();
        let second = offset_pointer_by_int32_elements(base.clone(), Bitvector32Term::Constant(1));
        let third = offset_pointer_by_int32_elements(base.clone(), Bitvector32Term::Constant(2));
        let local_i = Pointer {
            block: "local:i".to_string(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let initial_memory = memory_with_symbolic_valid_range_cells(
            CMemory::new(),
            &std::collections::BTreeMap::from([("p".to_string(), (base.clone(), 12))]),
        );
        let initial_resources =
            ResourceContext::new().with_resource(CResource::Write(CMemoryRange::new(
                base.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(3),
            )));
        let final_memory = initial_memory
            .clone()
            .with_block("local:i", 4)
            .store(first, int32(0))
            .store(second, int32(1))
            .store(third, int32(2))
            .store(local_i, int32(3));

        assert_eq!(
            verified.specification.state(),
            &CState::new()
                .with_memory(initial_memory)
                .with_resource_context(initial_resources.clone())
        );
        assert_eq!(verified.specification.arguments(), &[c_pointer_value(base)]);
        assert_eq!(
            verified.specification.outcome(),
            &CFunctionOutcome::Return {
                value: int32(2),
                state: CState::new()
                    .with_memory(final_memory)
                    .with_resource_context(initial_resources),
            }
        );
        assert_eq!(
            implication_body(verified.theorem.proposition()),
            &Proposition::CFunctionSatisfiesSpecification {
                function: syntax::parse_function(FILL3_C)
                    .expect("fill3 should parse")
                    .to_kernel_function()
                    .with_resource_summary(
                        vec![CResourceSpec::Write(CMemorySegment::new(
                            CExpression::Variable("p".to_string()),
                            CExpression::Value(int32(0)),
                            CExpression::Value(int32(3)),
                        ))],
                        Vec::new(),
                    ),
                specification: verified.specification.clone(),
            }
        );
    }

    #[test]
    fn signature_mismatch_reports_direct_error() {
        let source = FILL3_CLICK.replace("int32* p", "int32 q");
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong signature should fail");

        assert!(
            error.message().contains("signature mismatch"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn failed_ensure_reports_actual_return() {
        let source = FILL3_CLICK.replace("result == 2", "result == 3");
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong result should fail");

        assert!(
            error
                .message()
                .contains("left side evaluated to 2, right side evaluated to 3"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn failed_memory_postcondition_reports_loaded_value() {
        let source = FILL3_CLICK.replace(
            "ensures returns_second: result == 2",
            "ensures third: p[2] == 3",
        );
        let error = verify_c0_sources(&source, &[("fill3.c", FILL3_C)])
            .expect_err("wrong memory postcondition should fail");

        assert!(
            error
                .message()
                .contains("left side evaluated to 2, right side evaluated to 3"),
            "{}",
            error.message()
        );
    }
}
