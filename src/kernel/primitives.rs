use super::api::{int32, normalize_exact_memory_loads_in_pointer_offset, uint8};
use super::memory_provenance::{AtomicMemoryLoadEqualityEvidence, PointerOffsetEqualityEvidence};
use super::reasoning::{
    bitvector_terms_proven_equal_for_memory_resolution,
    c_values_proven_equal_for_memory_resolution, collect_or_cases, instantiate_range_fold_step,
    int32_element_index_from_offset, memory_snapshots_proven_equal_at_pointer,
    pointers_proven_distinct_for_memory_resolution, pointers_proven_equal_for_memory_resolution,
    resource_context_has_read, signed_bitvector_constant, signed_i64_bitvector_constant,
};
use std::collections::{BTreeMap, BTreeSet};

mod contracts;
mod memory_state;
mod proof_objects;
mod resource_algebra;
mod term_operations;
use memory_state::*;
pub(super) use proof_objects::*;
pub(super) use resource_algebra::*;

pub(super) const C_POINTER_BYTE_WIDTH: u32 = 8;
pub(super) const RANGE_FOLD_CONCRETE_UNROLL_LIMIT: i64 = 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable(pub u64);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    Condition,
    Bitvector32,
    PointerOffset,
    CType,
    CInt32,
    CPointer,
    CValue,
    CMemory,
    CState,
    CStatementOutcome,
    CFunctionOutcome,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Bitvector32Term {
    Constant(u32),
    Variable(Variable),
    Add(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Subtract(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Multiply(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Divide(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Remainder(Box<Bitvector32Term>, Box<Bitvector32Term>),
    ShiftLeft(Box<Bitvector32Term>, Box<Bitvector32Term>),
    ArithmeticShiftRight(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseAnd(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseOr(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseXor(Box<Bitvector32Term>, Box<Bitvector32Term>),
    BitwiseNot(Box<Bitvector32Term>),
    If {
        condition: Box<ConditionTerm>,
        then_term: Box<Bitvector32Term>,
        else_term: Box<Bitvector32Term>,
    },
    RangeFold {
        start: Box<Bitvector32Term>,
        end: Box<Bitvector32Term>,
        initial: Box<Bitvector32Term>,
        accumulator: Variable,
        item: Variable,
        body: Box<Bitvector32Term>,
    },
    /// An opaque application left by one-step unfolding of a total recursive
    /// pure Click function at symbolic arguments.
    PureFunctionApplication {
        name: String,
        arguments: Vec<Bitvector32Term>,
    },
    MemoryLoad(SharedCMemory, Box<Pointer>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PointerOffsetTerm {
    Constant(i64),
    Variable(Variable),
    Add(Box<PointerOffsetTerm>, Box<PointerOffsetTerm>),
    Int32Scaled {
        value: Box<Bitvector32Term>,
        byte_width: i64,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ConditionTerm {
    Constant(bool),
    Variable(Variable),
    Bitvector32SignedLessThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedLessEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedGreaterThan(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedGreaterEqual(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32Equal(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedAddOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedSubtractOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedMultiplyOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedDivideOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    Bitvector32SignedShiftLeftOverflows(Box<Bitvector32Term>, Box<Bitvector32Term>),
    PointerOffsetEqual(Box<PointerOffsetTerm>, Box<PointerOffsetTerm>),
    PointerEqual(Box<Pointer>, Box<Pointer>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Pointer {
    pub block: PointerBlock,
    pub offset: PointerOffsetTerm,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum PointerBlock {
    Concrete(String),
    ExternalArgument,
    Symbolic(Variable),
    /// A trusted allocation identity. Unlike a symbolic/opaque block, this is
    /// fresh and distinct from every other block identity.
    Heap(u64),
}

impl PointerBlock {
    pub(crate) fn starts_with(&self, prefix: &str) -> bool {
        matches!(self, Self::Concrete(name) if name.starts_with(prefix))
    }

    pub(crate) fn strip_prefix<'a>(&'a self, prefix: &str) -> Option<&'a str> {
        match self {
            Self::Concrete(name) => name.strip_prefix(prefix),
            Self::ExternalArgument | Self::Symbolic(_) | Self::Heap(_) => None,
        }
    }
}

impl From<String> for PointerBlock {
    fn from(name: String) -> Self {
        Self::Concrete(name)
    }
}

impl From<&str> for PointerBlock {
    fn from(name: &str) -> Self {
        Self::Concrete(name.to_string())
    }
}

impl std::fmt::Display for PointerBlock {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Concrete(name) => formatter.write_str(name),
            Self::ExternalArgument => formatter.write_str("arg-memory"),
            Self::Symbolic(variable) => write!(formatter, "symbolic-pointer:{}", variable.0),
            Self::Heap(identity) => write!(formatter, "heap-allocation:{identity}"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CValue {
    Void,
    Int32(Bitvector32Term),
    UInt8(Bitvector32Term),
    Pointer(Pointer),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CType {
    Void,
    Int32,
    UInt8,
    Int32Pointer,
    UInt8Pointer,
    Int32Array(u32),
    UInt8Array(u32),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLValue {
    pub(super) storage: CLValueStorage,
    pub(super) value_type: CType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLValueStorage {
    Local { name: String },
    Memory { pointer: Pointer },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpression {
    Value(CValue),
    Variable(String),
    AddressOf(Box<CExpression>),
    PointerOffsetBytes {
        pointer: Box<CExpression>,
        bytes: u32,
    },
    LessThan(Box<CExpression>, Box<CExpression>),
    LessEqual(Box<CExpression>, Box<CExpression>),
    GreaterThan(Box<CExpression>, Box<CExpression>),
    GreaterEqual(Box<CExpression>, Box<CExpression>),
    Equal(Box<CExpression>, Box<CExpression>),
    NotEqual(Box<CExpression>, Box<CExpression>),
    Not(Box<CExpression>),
    And(Box<CExpression>, Box<CExpression>),
    Or(Box<CExpression>, Box<CExpression>),
    Add(Box<CExpression>, Box<CExpression>),
    Subtract(Box<CExpression>, Box<CExpression>),
    Multiply(Box<CExpression>, Box<CExpression>),
    Divide(Box<CExpression>, Box<CExpression>),
    Remainder(Box<CExpression>, Box<CExpression>),
    ShiftLeft(Box<CExpression>, Box<CExpression>),
    ShiftRight(Box<CExpression>, Box<CExpression>),
    BitwiseAnd(Box<CExpression>, Box<CExpression>),
    BitwiseOr(Box<CExpression>, Box<CExpression>),
    BitwiseXor(Box<CExpression>, Box<CExpression>),
    BitwiseNot(Box<CExpression>),
    Load(Box<CExpression>),
    TypedLoad {
        pointer: Box<CExpression>,
        value_type: CType,
    },
    Index(Box<CExpression>, Box<CExpression>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CComparisonOperator {
    Equal,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecMemory {
    Current,
    FunctionEntry,
    LoopEntry,
    Fixed(CMemory),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecExpression {
    Value(CValue),
    CExpression(CExpression),
    CountedResourceCount {
        name: String,
        arguments: Vec<Option<SpecExpression>>,
    },
    Add(Box<SpecExpression>, Box<SpecExpression>),
    Subtract(Box<SpecExpression>, Box<SpecExpression>),
    Multiply(Box<SpecExpression>, Box<SpecExpression>),
    Divide(Box<SpecExpression>, Box<SpecExpression>),
    Remainder(Box<SpecExpression>, Box<SpecExpression>),
    ShiftLeft(Box<SpecExpression>, Box<SpecExpression>),
    ShiftRight(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseAnd(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseOr(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseXor(Box<SpecExpression>, Box<SpecExpression>),
    BitwiseNot(Box<SpecExpression>),
    If {
        condition: Box<SpecProposition>,
        then_branch: Box<SpecExpression>,
        else_branch: Box<SpecExpression>,
    },
    RangeFold {
        start: Box<SpecExpression>,
        end: Box<SpecExpression>,
        initial: Box<SpecExpression>,
        accumulator: String,
        item: String,
        body: Box<SpecExpression>,
    },
    Let {
        name: String,
        value: Box<SpecExpression>,
        body: Box<SpecExpression>,
    },
    PureFunctionApplication {
        name: String,
        arguments: Vec<SpecExpression>,
    },
    LoopEntrySnapshot(Box<SpecExpression>),
    PointerOffset {
        pointer: Box<SpecExpression>,
        elements: Box<SpecExpression>,
        byte_width: u32,
    },
    MemoryLoad {
        memory: SpecMemory,
        pointer: Box<SpecExpression>,
        value_type: CType,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecPredicateArgument {
    Value(SpecExpression),
    ArrayRef {
        memory: SpecMemory,
        pointer: SpecExpression,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecProposition {
    Comparison {
        left: SpecExpression,
        operator: CComparisonOperator,
        right: SpecExpression,
    },
    And(Box<SpecProposition>, Box<SpecProposition>),
    Or(Box<SpecProposition>, Box<SpecProposition>),
    Not(Box<SpecProposition>),
    Implies(Box<SpecProposition>, Box<SpecProposition>),
    ForAllInt32 {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    ExistsInt32 {
        name: String,
        variable: Variable,
        body: Box<SpecProposition>,
    },
    Predicate {
        name: String,
        arguments: Vec<SpecPredicateArgument>,
    },
    ResourceSeparate {
        left: SpecResource,
        right: SpecResource,
    },
    ResourceContains {
        parent: SpecResource,
        child: SpecResource,
    },
    MemoryLoadable {
        memory: SpecMemory,
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
        element_width: u32,
    },
    Defined(SpecExpression),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum SpecResource {
    Memory {
        base: SpecExpression,
        start: SpecExpression,
        end: SpecExpression,
    },
    Composite {
        name: String,
        arguments: Vec<SpecExpression>,
    },
    Token {
        name: String,
        arguments: Vec<SpecExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatement {
    Skip,
    Declare {
        name: String,
        c_type: CType,
    },
    Assign {
        name: String,
        expression: CExpression,
    },
    CallAssign {
        target: String,
        function_name: String,
        arguments: Vec<CExpression>,
    },
    Call {
        function_name: String,
        arguments: Vec<CExpression>,
    },
    /// Allocate a runtime-sized heap block and assign either null or its fresh
    /// base pointer to `target`.
    HeapAllocate {
        target: String,
        bytes: CExpression,
    },
    /// End the heap allocation named by `pointer`. Null is a no-op.
    HeapFree {
        pointer: CExpression,
    },
    Assert {
        condition: CExpression,
        label: Option<String>,
    },
    Seq(Box<CStatement>, Box<CStatement>),
    Return(CExpression),
    Store {
        pointer: CExpression,
        value: CExpression,
    },
    TypedStore {
        pointer: CExpression,
        value: CExpression,
        value_type: CType,
    },
    If {
        condition: CExpression,
        then_branch: Box<CStatement>,
        else_branch: Box<CStatement>,
    },
    While {
        condition: CExpression,
        invariant: Vec<Proposition>,
        invariant_checks: Vec<CLoopInvariantCheck>,
        effect_checks: Vec<CLoopEffectCheck>,
        body: Box<CStatement>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopInvariantCheck {
    pub(super) proposition: SpecProposition,
    pub(super) entry_context: Option<String>,
    pub(super) preservation_context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLoopEffectCheck {
    pub(super) effect: CLoopEffect,
    pub(super) span: CLoopEffectSpan,
    pub(super) context: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffect {
    Immutable,
    Mutable(Vec<CMemorySegment>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CLoopEffectSpan {
    Whole,
    Step,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemorySegment {
    pub(super) base: CExpression,
    pub(super) start: CExpression,
    pub(super) end: CExpression,
    /// An optional entry-state condition guarding a contract footprint.
    /// Resource and loop segments are normally unconditional.
    pub(super) guard: Option<SpecProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemoryRange {
    pub(super) base: Pointer,
    pub(super) start: Bitvector32Term,
    pub(super) end: Bitvector32Term,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CParameter {
    pub(super) name: String,
    pub(super) c_type: CType,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunction {
    pub(super) return_type: CType,
    pub(super) name: String,
    pub(super) parameters: Vec<CParameter>,
    pub(super) body: CStatement,
    pub(super) source_body: CStatement,
    pub(super) resource_requires: Vec<CResourceSpec>,
    pub(super) resource_ensures: Vec<CResourceSpec>,
    pub(super) contract_requires: Vec<SpecProposition>,
    pub(super) contract_ensures: Vec<SpecProposition>,
    pub(super) contract_mutable: Vec<CMemorySegment>,
    pub(super) contract_claims: Vec<CFunctionContractClaim>,
    pub(super) opaque_contract_supported: bool,
    pub(super) composite_resource_definitions: Vec<CCompositeResourceDefinition>,
    /// Contract-local definitions for opaque Click predicate requirements.
    /// Both sides are instantiated at the exact function entry state.
    pub(super) predicate_unfoldings: Vec<CPredicateUnfolding>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CPredicateUnfolding {
    pub(super) predicate: SpecProposition,
    pub(super) body: SpecProposition,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CCompositeResourceDefinition {
    pub(super) name: String,
    pub(super) parameters: Vec<CParameter>,
    pub(super) condition: Option<SpecProposition>,
    pub(super) recursive: bool,
    pub(super) counted_population: bool,
    pub(super) contains: Vec<CResourceSpec>,
    pub(super) facts: Vec<SpecProposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionContractClaimKey {
    BodySafety,
    Effect(usize),
    Ensure(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionContractClaim {
    pub(super) key: CFunctionContractClaimKey,
    pub(super) target: CFunctionContractClaimTarget,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionContractClaimTarget {
    BodySafety,
    Effect,
    EnsureProposition(usize),
    EnsureResource(usize),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionSpecification {
    pub(super) state: CState,
    pub(super) arguments: Vec<CExpression>,
    pub(super) requires: Vec<Proposition>,
    pub(super) outcome: CFunctionOutcome,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CExecutionEnvironment {
    pub(super) functions: std::sync::Arc<BTreeMap<String, CFunction>>,
    pub(super) verified_function_rules: std::sync::Arc<BTreeMap<String, CVerifiedFunctionRule>>,
    pub(super) verified_function_termination_rules:
        std::sync::Arc<BTreeMap<String, CVerifiedFunctionTerminationRule>>,
    pub(super) verified_loop_rules: std::sync::Arc<Vec<CVerifiedLoopRule>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CCallSemantics {
    ExecuteBodies,
    ApplyVerifiedRules,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CLoopSemantics {
    Verify,
    ApplyVerifiedRules,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CExecutionSemantics {
    pub calls: CCallSemantics,
    pub loops: CLoopSemantics,
}

impl CExecutionSemantics {
    pub const EXECUTE_BODIES: Self = Self {
        calls: CCallSemantics::ExecuteBodies,
        loops: CLoopSemantics::Verify,
    };

    pub const APPLY_VERIFIED_RULES: Self = Self {
        calls: CCallSemantics::ApplyVerifiedRules,
        loops: CLoopSemantics::ApplyVerifiedRules,
    };

    pub const APPLY_CALL_RULES_AND_VERIFY_LOOPS: Self = Self {
        calls: CCallSemantics::ApplyVerifiedRules,
        loops: CLoopSemantics::Verify,
    };
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionRule {
    pub(super) function: CFunction,
}

/// Kernel evidence that a partially-correct C function also returns.
///
/// Construction is deliberately separate from [`CVerifiedFunctionRule`], so
/// ordinary opaque calls never acquire a total-correctness assumption.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionTerminationRule {
    pub(super) function: CFunction,
}

/// An untrusted surface-language proposal for ranking the cycles in one C
/// function. The kernel checks every supplied index and variable against the
/// exact body before producing termination evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionTerminationPlan {
    pub(super) function_name: String,
    pub(super) recursive_measure: Option<CFunctionTerminationMeasure>,
    pub(super) loop_measures: BTreeMap<usize, String>,
}

impl CFunctionTerminationPlan {
    pub fn function_name(&self) -> &str {
        &self.function_name
    }

    pub fn extend_loop_measures(&mut self, measures: impl IntoIterator<Item = (usize, String)>) {
        self.loop_measures.extend(measures);
    }
}

/// An untrusted description of the function-level ranking candidate. The
/// termination checker resolves the selected parameter or exact contract
/// resource again against the verified function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CFunctionTerminationMeasure {
    NumericParameter(usize),
    ResourceRequirement(usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CTerminationError {
    pub(super) message: String,
}

impl CVerifiedFunctionTerminationRule {
    pub fn function_name(&self) -> &str {
        self.function.name()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedFunctionContractClaim {
    pub(super) function: CFunction,
    pub(super) key: CFunctionContractClaimKey,
}

impl CVerifiedFunctionContractClaim {
    pub fn key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedLoopRule {
    pub(super) symbolic_entry_state: CState,
    pub(super) loop_statement: CStatement,
    pub(super) required_assumptions: PureFactContext,
    pub(super) paths: Vec<CStatementExecutionPath>,
    pub(super) composite_resource_definitions: Vec<CCompositeResourceDefinition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUndefinedBehavior {
    SignedOverflow,
    DivisionByZero,
    InvalidShift,
    InvalidMemory,
    UninitializedRead,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CInvalidFree {
    InteriorPointer,
    NonHeapPointer,
    DoubleFree,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    IndeterminatePointeeType,
    WrongArity {
        expected: usize,
        actual: usize,
    },
    MissingReturn,
    MissingResource {
        resource: CResourceFact,
    },
    MissingVerifiedFunctionRule(String),
    UnsupportedOpaqueFunctionContract(String),
    FunctionContract(String),
    InvalidFree(CInvalidFree),
    UnresolvedAllocationOutcome,
    LiveAllocationLeak {
        allocation: CResourceFact,
    },
    StaleResourceAfterFree {
        resource: CResourceFact,
    },
    DuplicateResource {
        resource: CResourceFact,
    },
    OverlappingWriteResources {
        left: Box<CMemoryRange>,
        right: Box<CMemoryRange>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ExecutionLimit {
    Deadline,
    ExpressionSteps,
    StatementSteps,
    FunctionCalls,
    LoopUnrolls,
    Paths,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionBudget {
    pub(super) expression_steps: usize,
    pub(super) statement_steps: usize,
    pub(super) function_calls: usize,
    pub(super) loop_unrolls: usize,
    pub(super) paths: usize,
    pub(super) next_opaque_call: u64,
    pub(super) next_verification_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpressionOutcome {
    Value(CValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CConditionOutcome {
    Value(bool),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLValueOutcome {
    LValue(CLValue),
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatementOutcome {
    Normal(CState),
    Return {
        value: CValue,
        state: CState,
    },
    /// Internal to `CStatementVerifies`: the statement has no finite
    /// successor, but all of its finite prefixes have been checked.
    VerificationDiverges,
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionOutcome {
    Return {
        value: CValue,
        state: CState,
    },
    /// Internal to `CFunctionVerifies`: no return frontier exists, but the
    /// function's finite prefixes satisfy its safety proof.
    VerificationDiverges,
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CLocalEnvironment {
    pub(super) bindings: std::sync::Arc<BTreeMap<String, CLocalBinding>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLocalBinding {
    Object { value: CValue, c_type: CType },
    UninitializedObject { c_type: CType },
    ArrayObject { element_type: CType, length: u32 },
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemory {
    pub(super) blocks: std::sync::Arc<BTreeMap<PointerBlock, CBlock>>,
    pub(super) cells: std::sync::Arc<BTreeMap<Pointer, CValue>>,
    pub(super) heap: std::sync::Arc<CHeapMemory>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CHeapMemory {
    /// Live heap blocks are also present in `blocks`; this set distinguishes
    /// them from automatic storage and memory-havoc markers.
    pub(super) live_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// Heap identities are never reused within a proof. Keeping retired
    /// identities makes double-free and stale-pointer checks explicit.
    pub(super) retired_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// A malloc result whose null/success outcome has not yet been refined by
    /// control flow or direct return. Pending allocations carry no authority
    /// until resolved.
    pub(super) pending_allocations: BTreeMap<Pointer, Bitvector32Term>,
    /// Successful malloc storage remains uninitialized until individual
    /// cells are written. Contract-imported allocations are not placed here.
    pub(super) uninitialized_allocations: BTreeSet<Pointer>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CBlock {
    pub(super) size: Bitvector32Term,
}

/// An interned, immutable memory snapshot for embedding inside terms.
///
/// Equality and hashing are O(1) via the arena identity and a precomputed
/// content hash; ordering keeps a same-identity fast path but falls back to
/// structural comparison so BTreeMap iteration order stays the structural
/// order (proof search is sensitive to iteration order, and arena-insertion
/// order would be nondeterministic across replays).
#[derive(Clone)]
pub struct SharedCMemory {
    arena: u32,
    id: u32,
    content_hash: u64,
    memory: std::sync::Arc<CMemory>,
}

impl SharedCMemory {
    /// How this snapshot was produced, when the arena that named it is this
    /// thread's and an edge producer recorded one.
    ///
    /// `None` is always a legitimate answer — for entry states, for
    /// snapshots built by paths that record no edge, for handles that
    /// crossed a thread, and for every snapshot when
    /// `CLICK_DISABLE_MEMORY_DAG` is set. Consumers fall back rather than
    /// conclude anything from the absence.
    pub(crate) fn derivation(&self) -> Option<std::sync::Arc<CMemoryDerivation>> {
        if memory_dag_disabled() {
            return None;
        }
        C_MEMORY_ARENA.with(|(token, arena)| {
            if *token != self.arena {
                return None;
            }
            arena
                .borrow()
                .derivations
                .get(self.id as usize)
                .cloned()
                .flatten()
        })
    }

    /// The arena id naming this snapshot, valid only against ids from the
    /// same arena. Strictly decreasing along `derivation().base()`, which is
    /// what makes DAG walks terminate.
    pub(crate) fn arena_id(&self) -> (u32, u32) {
        (self.arena, self.id)
    }

    pub(crate) fn memory(&self) -> &CMemory {
        &self.memory
    }
}

impl PartialEq for SharedCMemory {
    fn eq(&self, other: &Self) -> bool {
        if self.arena == other.arena {
            return self.id == other.id;
        }
        self.content_hash == other.content_hash && self.memory == other.memory
    }
}

impl Eq for SharedCMemory {}

impl std::hash::Hash for SharedCMemory {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_hash);
    }
}

impl Ord for SharedCMemory {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self.arena == other.arena && self.id == other.id {
            return std::cmp::Ordering::Equal;
        }
        self.memory.cmp(&other.memory)
    }
}

impl PartialOrd for SharedCMemory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::fmt::Debug for SharedCMemory {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.memory.fmt(formatter)
    }
}

impl std::ops::Deref for SharedCMemory {
    type Target = CMemory;

    fn deref(&self) -> &CMemory {
        &self.memory
    }
}

impl AsRef<CMemory> for SharedCMemory {
    fn as_ref(&self) -> &CMemory {
        &self.memory
    }
}

impl From<CMemory> for SharedCMemory {
    fn from(memory: CMemory) -> Self {
        intern_c_memory(memory)
    }
}

impl From<&CMemory> for SharedCMemory {
    fn from(memory: &CMemory) -> Self {
        intern_c_memory_ref(memory)
    }
}

/// How a memory snapshot was produced from an earlier one: the edges of the
/// named-memory-state DAG (`docs/advanced/memory-dag.md`). Each
/// variant names its base snapshot, so following `base` walks backwards
/// through the write history that execution already knew when it built the
/// snapshot — instead of reconstructing that history at proof time from
/// recorded effect facts.
///
/// A derivation is **advisory**. It only ever states a true fact about how a
/// snapshot arose, so every consumer must fall back to its previous
/// reasoning when none is present; nothing may depend on one existing. That
/// is what lets `CLICK_DISABLE_MEMORY_DAG` restore the pre-arc path exactly,
/// and why a snapshot interned on another thread (the arena is thread-local)
/// is merely slower to reason about rather than wrong.
///
/// `LoopHavoc` is deliberately its own edge kind rather than a bulk store:
/// loop havoc has no write set for a pointer to be disjoint from, so no
/// load-preservation walk may cross one. Enforcing that at the edge is how
/// havoc identity survives this arc by construction, upstream of any
/// snapshot comparison (see conventions.md's soundness trap).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CMemoryDerivation {
    /// `base` with one cell written.
    Store {
        base: SharedCMemory,
        pointer: Pointer,
        value: CValue,
    },
    /// `base` with one block declared; no cell changes, so every load reads
    /// exactly what it read in `base`. This fourth edge kind was added after
    /// the initial DAG arc; without it, block declaration split the DAG into
    /// disjoint components ("arena identity is connected, arena derivations
    /// are not"). The havoc producers insert their marker
    /// blocks directly rather than through [`CMemory::with_block`], so this
    /// edge can never alias a havoc hop.
    BlockDeclared {
        base: SharedCMemory,
        block: PointerBlock,
    },
    /// `base` with one fresh, uninitialized heap block made live.
    HeapAllocated {
        base: SharedCMemory,
        block: PointerBlock,
        bytes: Bitvector32Term,
    },
    /// `base` with one unresolved allocation result registered. Pending
    /// metadata changes no program-observable memory, so every existing load
    /// is preserved across this edge.
    HeapAllocationPending {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with one complete heap allocation lifetime ended.
    ///
    /// `allocation_base` is kept rather than only its broad pointer block:
    /// allocations imported from contracts can be subranges of external
    /// memory, where retiring the whole `ExternalArgument` block would also
    /// retire unrelated objects.
    HeapFreed {
        base: SharedCMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    /// `base` with some cached cell values forgotten at one program point:
    /// the write path narrows the cell map before storing
    /// (`without_possible_aliasing_cells`), which changes the spelling but
    /// not the state, so every load still reads exactly what it read in
    /// `base`. Recorded ONLY where forgetting is unconditional; the
    /// case-split prune in the load path (`without_cell` under an assumed
    /// distinctness branch) must never record one, because its two spellings
    /// agree only under that branch's assumption. Havoc forgetting keeps its
    /// own never-crossed / guarded edge kinds, so this edge cannot launder a
    /// havoc (conventions.md's soundness trap).
    CellsForgotten { base: SharedCMemory },
    /// `base` after a loop body that may write anything it can reach.
    LoopHavoc {
        base: SharedCMemory,
        variable: Variable,
    },
    /// `base` after a call that may write only within `mutable_ranges`.
    CallHavoc {
        base: SharedCMemory,
        variable: Variable,
        mutable_ranges: Vec<CMemoryRange>,
    },
}

impl CMemoryDerivation {
    /// The snapshot this one was derived from.
    pub fn base(&self) -> &SharedCMemory {
        match self {
            Self::Store { base, .. }
            | Self::BlockDeclared { base, .. }
            | Self::HeapAllocated { base, .. }
            | Self::HeapAllocationPending { base, .. }
            | Self::HeapFreed { base, .. }
            | Self::CellsForgotten { base }
            | Self::LoopHavoc { base, .. }
            | Self::CallHavoc { base, .. } => base,
        }
    }
}

/// True when `CLICK_DISABLE_MEMORY_DAG` is set: derivations are neither
/// recorded nor reported, so every consumer takes its pre-arc path. The A/B
/// handle for the named-memory-states arc.
pub(crate) fn memory_dag_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("CLICK_DISABLE_MEMORY_DAG").is_some())
}

static NEXT_MEMORY_ARENA_TOKEN: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

#[derive(Default)]
struct CMemoryArena {
    identities: std::collections::HashMap<std::sync::Arc<CMemory>, (u32, u64)>,
    shallow_identities: std::collections::HashMap<CMemoryShallowIdentity, (u32, u64)>,
    memories: Vec<std::sync::Arc<CMemory>>,
    /// Indexed by arena id; `None` for entry states and for any snapshot
    /// whose first interning did not come from a recorded edge.
    derivations: Vec<Option<std::sync::Arc<CMemoryDerivation>>>,
}

#[derive(Clone, Copy, Eq, Hash, PartialEq)]
struct CMemoryShallowIdentity {
    blocks: usize,
    cells: usize,
    heap: usize,
}

impl CMemoryShallowIdentity {
    fn of(memory: &CMemory) -> Self {
        Self {
            blocks: std::sync::Arc::as_ptr(&memory.blocks) as usize,
            cells: std::sync::Arc::as_ptr(&memory.cells) as usize,
            heap: std::sync::Arc::as_ptr(&memory.heap) as usize,
        }
    }
}

thread_local! {
    static C_MEMORY_ARENA: (u32, std::cell::RefCell<CMemoryArena>) = (
        NEXT_MEMORY_ARENA_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        std::cell::RefCell::new(CMemoryArena::default()),
    );
    static C_MEMORY_DERIVATION_GENERATION: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Bumped every time a derivation slot is filled. Memo tables over DAG walks
/// key on this so an edge recorded later invalidates earlier "no path"
/// answers instead of leaving them stale.
pub(super) fn c_memory_derivation_generation() -> u64 {
    C_MEMORY_DERIVATION_GENERATION.with(std::cell::Cell::get)
}

/// Records that `result` is `derivation` applied to its base, unless
/// `result` already carries a derivation.
///
/// **First-wins is load-bearing, not a cache policy.** A derivation's base
/// must already be interned in order to be named, so it always holds a
/// strictly smaller arena id than a *newly* assigned one. Keeping the first
/// derivation therefore makes `base.id < derived.id` an arena-wide
/// invariant, and cycles unrepresentable rather than merely unlikely. Two
/// otherwise easy cycles are closed by exactly this: a store whose value
/// equals the cell already there (the result re-interns to its own base, so
/// `base.id == result.id` and the edge is dropped), and a store-then-store-
/// back pair (the second result re-interns to the earlier node and keeps
/// that node's older derivation). Callers may rely on any walk over `base`
/// terminating; a hop cap still depth-gates them, per conventions.md.
pub(crate) fn record_c_memory_derivation(result: &CMemory, derivation: CMemoryDerivation) {
    if memory_dag_disabled() {
        return;
    }
    // Interning borrows the arena, so it has to finish before the write.
    let derived = intern_c_memory_ref(result);
    C_MEMORY_ARENA.with(|(token, arena)| {
        if *token != derived.arena || *token != derivation.base().arena {
            return;
        }
        let mut arena = arena.borrow_mut();
        let Some(slot) = arena.derivations.get_mut(derived.id as usize) else {
            return;
        };
        if slot.is_some() || derivation.base().id >= derived.id {
            return;
        }
        *slot = Some(std::sync::Arc::new(derivation));
        C_MEMORY_DERIVATION_GENERATION.with(|generation| generation.set(generation.get() + 1));
    });
}

fn c_memory_content_hash(memory: &CMemory) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    memory.hash(&mut hasher);
    hasher.finish()
}

fn record_c_memory_structural_lookup_work(memory: &CMemory) {
    crate::instrumentation::record_deterministic_work(
        memory.blocks.len()
            + memory.cells.len()
            + memory.heap.live_allocations.len()
            + memory.heap.retired_allocations.len()
            + memory.heap.pending_allocations.len()
            + memory.heap.uninitialized_allocations.len(),
    );
}

/// Interns a memory snapshot in the thread-local arena. Structurally equal
/// snapshots interned on the same thread share one allocation and identity;
/// snapshots that cross threads still compare correctly through the content
/// hash and structural fallback.
pub fn intern_c_memory(memory: CMemory) -> SharedCMemory {
    C_MEMORY_ARENA.with(|(token, arena)| {
        let mut arena = arena.borrow_mut();
        let shallow_identity = CMemoryShallowIdentity::of(&memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_c_memory_structural_lookup_work(&memory);
        if let Some((stored, (id, content_hash))) = arena.identities.get_key_value(&memory) {
            return SharedCMemory {
                arena: *token,
                id: *id,
                content_hash: *content_hash,
                memory: stored.clone(),
            };
        }
        let id = u32::try_from(arena.identities.len()).expect("memory arena exhausted");
        let content_hash = c_memory_content_hash(&memory);
        let stored = std::sync::Arc::new(memory);
        arena.identities.insert(stored.clone(), (id, content_hash));
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: stored,
        }
    })
}

/// Interns by reference: an already-interned snapshot is found without
/// cloning it, so hot memoization lookups keyed by interned identity pay a
/// hash and comparison but no allocation.
pub fn intern_c_memory_ref(memory: &CMemory) -> SharedCMemory {
    C_MEMORY_ARENA.with(|(token, arena)| {
        let mut arena = arena.borrow_mut();
        let shallow_identity = CMemoryShallowIdentity::of(memory);
        if let Some((id, content_hash)) = arena.shallow_identities.get(&shallow_identity).copied() {
            return SharedCMemory {
                arena: *token,
                id,
                content_hash,
                memory: arena.memories[id as usize].clone(),
            };
        }
        record_c_memory_structural_lookup_work(memory);
        if let Some((stored, (id, content_hash))) = arena.identities.get_key_value(memory) {
            return SharedCMemory {
                arena: *token,
                id: *id,
                content_hash: *content_hash,
                memory: stored.clone(),
            };
        }
        let id = u32::try_from(arena.identities.len()).expect("memory arena exhausted");
        let content_hash = c_memory_content_hash(memory);
        let stored = std::sync::Arc::new(memory.clone());
        arena.identities.insert(stored.clone(), (id, content_hash));
        arena
            .shallow_identities
            .insert(shallow_identity, (id, content_hash));
        arena.memories.push(stored.clone());
        arena.derivations.push(None);
        SharedCMemory {
            arena: *token,
            id,
            content_hash,
            memory: stored,
        }
    })
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CState {
    pub(super) locals: CLocalEnvironment,
    pub(super) memory: CMemory,
    pub(super) resources: ResourceContext,
    pub(super) counted_populations: std::sync::Arc<Vec<CCountedPopulation>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CCountedPopulation {
    pub(super) name: String,
    pub(super) arguments: Vec<CValue>,
    pub(super) count: Bitvector32Term,
    /// Marks observation of a resource family even while its exact population
    /// is zero. Marker entries are not themselves resource populations.
    pub(super) family_observation_marker: bool,
}

#[derive(Clone, Debug, Default)]
pub struct ResourceContext {
    pub(super) facts: std::sync::Arc<Vec<CResourceFact>>,
    pub(super) index: std::sync::Arc<std::sync::OnceLock<ResourceContextIndex>>,
}

#[derive(Debug, Default)]
pub(super) struct ResourceContextIndex {
    pub(super) exact: BTreeMap<CResourceFact, Vec<usize>>,
    pub(super) by_resource: BTreeMap<CResource, Vec<usize>>,
    pub(super) exact_shapes: BTreeMap<(ResourceFamily, String, usize), Vec<usize>>,
    pub(super) memory_by_block: BTreeMap<PointerBlock, Vec<usize>>,
    pub(super) memory_starts: BTreeMap<(PointerBlock, bool, Bitvector32Term), Vec<usize>>,
    pub(super) memory_ends: BTreeMap<(PointerBlock, bool, Bitvector32Term), Vec<usize>>,
    pub(super) concrete_memory_by_base: BTreeMap<(Pointer, bool), BTreeMap<(u32, u32), Vec<usize>>>,
}

impl PartialEq for ResourceContext {
    fn eq(&self, other: &Self) -> bool {
        self.facts == other.facts
    }
}

impl Eq for ResourceContext {}

impl std::hash::Hash for ResourceContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.facts.hash(state);
    }
}

impl Ord for ResourceContext {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.facts.cmp(&other.facts)
    }
}

impl PartialOrd for ResourceContext {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceFact {
    Own(CResource, Box<Bitvector32Term>),
    View(CResource),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResource {
    Memory(CMemoryRange),
    Composite {
        name: String,
        arguments: Vec<CValue>,
    },
    Token {
        name: String,
        arguments: Vec<CValue>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceContextValidityError {
    DuplicateOwnedResourceFact(CResourceFact),
    OverlappingWriteResources {
        left: CMemoryRange,
        right: CMemoryRange,
    },
}

/// The result of consuming one available resource fact to satisfy a required
/// fact. Viewed facts are normally preserved; owned facts may be removed or
/// replaced by residual ownership.
pub(super) enum ResourceFactConsumption {
    Preserve,
    Replace(Vec<CResourceFact>),
}

/// The algebraic behavior supplied by one resource family.
///
/// `ResourceContext` provides state-level composition. Families define when
/// same-family facts are valid together, how one fact entails or satisfies
/// another, how consumed ownership leaves residues, how redundant facts are
/// normalized, and which facts are observable from a valid composition.
pub(super) trait ResourceFamilyAlgebra {
    fn family(&self) -> ResourceFamily;

    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceContextValidityError>;

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> bool;

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<ResourceFactConsumption>;

    /// Returns one fact equivalent to composing this pair when the pair can be
    /// losslessly normalized. `None` leaves both facts in the resource state.
    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &PureFactContext,
    ) -> Option<CResourceFact>;

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact>;

    fn observable_facts(
        &self,
        facts: &[&CResourceFact],
        assumptions: &PureFactContext,
    ) -> Vec<Proposition>;
}

struct MemoryResourceAlgebra;
struct TokenResourceAlgebra;
/// The kernel algebra for a folded composite fact is exact-match ownership and
/// viewing. Source-declared body equivalences are applied as fold, unfold, and
/// observation laws by the Click proof layer.
struct CompositeResourceAlgebra;

static MEMORY_RESOURCE_ALGEBRA: MemoryResourceAlgebra = MemoryResourceAlgebra;
static TOKEN_RESOURCE_ALGEBRA: TokenResourceAlgebra = TokenResourceAlgebra;
static COMPOSITE_RESOURCE_ALGEBRA: CompositeResourceAlgebra = CompositeResourceAlgebra;

/// Primitive resource families. Adding a variant also requires registering one
/// `ResourceFamilyAlgebra` implementation in `resource_family_algebra`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ResourceFamily {
    Memory,
    Composite,
    Token,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceAccessMode {
    Own,
    View,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceSpec {
    Read(CMemorySegment),
    Write(CMemorySegment),
    Quantified {
        quantity: CExpression,
        resource: Box<CResourceSpec>,
    },
    Composite {
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    },
    Token {
        access: CResourceAccessMode,
        name: String,
        arguments: Vec<CExpression>,
        parameter_types: Vec<CType>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Term {
    Condition(ConditionTerm),
    Bitvector32(Bitvector32Term),
    PointerOffset(PointerOffsetTerm),
    CValue(CValue),
    CExpressionOutcome(CExpressionOutcome),
    CStatementOutcome(CStatementOutcome),
    CFunctionOutcome(CFunctionOutcome),
    CMemory(CMemory),
    CState(CState),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Proposition {
    Equal(Term, Term),
    ConditionIs(ConditionTerm, bool),
    Predicate {
        name: String,
        arguments: Vec<Term>,
    },
    CExpressionEvaluates {
        state: CState,
        expression: CExpression,
        outcome: CExpressionOutcome,
    },
    CConditionEvaluates {
        state: CState,
        condition: CExpression,
        outcome: CConditionOutcome,
    },
    CStatementExecutes {
        state: CState,
        statement: CStatement,
        outcome: CStatementOutcome,
    },
    /// An abstract verification transition. Unlike `CStatementExecutes`, this
    /// does not assert that the represented outcome is concretely reachable.
    CStatementVerifies {
        state: CState,
        statement: CStatement,
        outcome: CStatementOutcome,
    },
    CFunctionExecutes {
        state: CState,
        function: CFunction,
        arguments: Vec<CExpression>,
        outcome: CFunctionOutcome,
    },
    /// A return branch admitted by modular verification. This is conditional
    /// on the function returning and is not a termination or reachability
    /// theorem.
    CFunctionVerifies {
        state: CState,
        function: CFunction,
        arguments: Vec<CExpression>,
        outcome: CFunctionOutcome,
    },
    CFunctionSatisfiesSpecification {
        function: CFunction,
        specification: CFunctionSpecification,
    },
    /// The specification describes one allowed return branch and makes no
    /// claim that the branch is reachable or that the function terminates.
    CFunctionPartiallySatisfiesSpecification {
        function: CFunction,
        specification: CFunctionSpecification,
    },
    CMemoryLoads {
        memory: CMemory,
        pointer: Pointer,
        outcome: CExpressionOutcome,
    },
    CMemoryCanStore {
        memory: CMemory,
        pointer: Pointer,
        byte_width: u32,
    },
    CMemoryLoadable {
        memory: CMemory,
        base: Pointer,
        bytes: Bitvector32Term,
    },
    CMemoryDisjoint {
        left_base: Pointer,
        left_start: Bitvector32Term,
        left_end: Bitvector32Term,
        right_base: Pointer,
        right_start: Bitvector32Term,
        right_end: Bitvector32Term,
    },
    CResourceSeparate {
        left: CResource,
        right: CResource,
    },
    /// Internal carrier for an already-validated resource composition.
    /// PureFactContext store this as indexed kernel authority rather than as an
    /// ambient proposition visible to proof search.
    CResourceComposition(ResourceContext),
    CResourceContains {
        parent: CResource,
        child: CResource,
    },
    CMemoryMutatesOnly {
        before: CMemory,
        after: CMemory,
        pointers: Vec<Pointer>,
    },
    CMemoryEffectSummary {
        before: CMemory,
        after: CMemory,
        mutable_ranges: Vec<CMemoryRange>,
    },
    CHeapLifetimeRetired {
        before: CMemory,
        after: CMemory,
        allocation_base: Pointer,
        bytes: Bitvector32Term,
    },
    CWhileInvariantRule {
        state: CState,
        condition: CExpression,
        invariant: Vec<Proposition>,
        body: CStatement,
        preserved: Vec<Proposition>,
        postcondition: Box<Proposition>,
    },
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Not(Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    ForAll {
        var: Variable,
        sort: Sort,
        body: Box<Proposition>,
    },
    Exists {
        name: String,
        var: Variable,
        sort: Sort,
        body: Box<Proposition>,
    },
}

/// An abstract proven proposition produced by kernel axioms.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Theorem {
    pub(super) proposition: std::sync::Arc<Proposition>,
}

/// Kernel-issued authority for a closed pure theorem that may be used during
/// whole-contract certification. The private field prevents the Click layer
/// from promoting an arbitrary proposition or unrelated theorem object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CVerifiedPureTheorem {
    pub(super) theorem: Theorem,
}

/// A proof tree produced by contextual proposition reasoning.
///
/// Smart reasoning may search for this tree. Replay only checks the selected
/// rule and its explicit children; it never searches for an alternative proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PropositionDerivation {
    pub(super) conclusion: Proposition,
    pub(super) rule: PropositionDerivationRule,
}

/// One exact signed-order edge retained by an atomic derivation.
///
/// The edge is oriented from `lower` to `upper`; `strict` distinguishes `<`
/// from `<=`. Certificate consumers can spell this ordered path directly
/// instead of rediscovering it from an unordered premise set.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignedOrderDerivationStep {
    pub(super) lower: Bitvector32Term,
    pub(super) upper: Bitvector32Term,
    pub(super) strict: bool,
    pub(super) premise: Proposition,
}

/// One exact ground-int32 equality edge retained in the orientation selected
/// by an atomic derivation. `premise` is the exact context proposition; the
/// source/target orientation may be the reverse of its written equality.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitvectorEqualityDerivationStep {
    pub(super) source: Bitvector32Term,
    pub(super) target: Bitvector32Term,
    pub(super) premise: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PropositionDerivationRule {
    ContextFree,
    ContextualAtomic {
        premises: PureFactContext,
        premises_id: u64,
        for_simp: bool,
        evidence: AtomicPropositionDerivationEvidence,
    },
    Explosion {
        premises: PureFactContext,
    },
    And {
        left: Box<PropositionDerivation>,
        right: Box<PropositionDerivation>,
    },
    OrLeft(Box<PropositionDerivation>),
    OrRight(Box<PropositionDerivation>),
    DoubleNegation(Box<PropositionDerivation>),
    Implies {
        antecedent: Proposition,
        body: Box<PropositionDerivation>,
    },
    ImpliesFalseAntecedent(Box<PropositionDerivation>),
    ForAllBody(Box<PropositionDerivation>),
    FiniteForAll {
        instances: Vec<PropositionDerivation>,
    },
    FiniteContextSplit {
        variable: Variable,
        lower: i64,
        upper: i64,
        premises: PureFactContext,
        instances: Vec<PropositionDerivation>,
    },
    DisjunctionCases {
        disjunction: Proposition,
        cases: Vec<PropositionDerivation>,
    },
    /// Case analysis on an assumed upper bound: `variable <= pivot` splits
    /// into `variable < pivot` and `variable == pivot`. `bound` is the exact
    /// assumed condition that licenses the split.
    UpperBoundSplit {
        bound: ConditionTerm,
        variable: Variable,
        pivot: Bitvector32Term,
        below: Box<PropositionDerivation>,
        at: Box<PropositionDerivation>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Int32IncrementBoundsEvidence {
    pub(super) lower_bound: SignedOrderDerivationStep,
    pub(super) upper_bound: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Int32PredecessorUpperBoundEvidence {
    pub(super) nonnegative: SignedOrderDerivationStep,
    pub(super) upper_bound: SignedOrderDerivationStep,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Int32LeAndNotLtEqualityEvidence {
    pub(super) less_equal: Proposition,
    pub(super) not_less_than: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Int32GeAndNotGtEqualityEvidence {
    pub(super) greater_equal: Proposition,
    pub(super) not_greater_than: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum AtomicPropositionDerivationEvidence {
    MemoryDag(AtomicMemoryLoadEqualityEvidence),
    PointerOffsetMemoryDag(PointerOffsetEqualityEvidence),
    BitvectorEqualityPath(Vec<BitvectorEqualityDerivationStep>),
    SignedOrderPath(Vec<SignedOrderDerivationStep>),
    Int32IncrementUpperBound(SignedOrderDerivationStep),
    Int32IncrementStrictlyIncreases(SignedOrderDerivationStep),
    Int32IncrementBelowMaxIsDefined(SignedOrderDerivationStep),
    Int32IncrementLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementGreaterEqualLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementStrictGreaterLowerBound(Box<Int32IncrementBoundsEvidence>),
    Int32IncrementPreservesOrder(Box<Int32IncrementBoundsEvidence>),
    Int32PositivePredecessorIsNonnegative(SignedOrderDerivationStep),
    Int32PositivePredecessorStrictlyDecreases(SignedOrderDerivationStep),
    Int32NonnegativePredecessorUpperBound(Box<Int32PredecessorUpperBoundEvidence>),
    Int32OneLePredecessorIsNonnegative(SignedOrderDerivationStep),
    Int32OneLePredecessorStrictlyDecreases(SignedOrderDerivationStep),
    Int32LeAndNotLtImpliesEquality(Box<Int32LeAndNotLtEqualityEvidence>),
    Int32GeAndNotGtImpliesEquality(Box<Int32GeAndNotGtEqualityEvidence>),
    Legacy,
}

#[derive(Clone, Debug, Default)]
pub struct PureFactContext {
    pub(super) condition_facts: crate::persistent::PersistentMap<ConditionTerm, bool>,
    /// Exact signed-order bounds keyed by either endpoint. Counts preserve
    /// synonymous condition spellings when one source fact is replaced.
    pub(super) signed_order_bounds: crate::persistent::PersistentMap<
        Bitvector32Term,
        crate::persistent::PersistentMap<(Bitvector32Term, bool, bool), usize>,
    >,
    /// Condition facts containing a memory-load atom, indexed by the loaded
    /// pointer's snapshot-blind structural fingerprint. This is derived from
    /// `condition_facts`; it narrows snapshot-aware load-spelling checks
    /// without deciding them.
    pub(super) memory_load_condition_facts:
        std::sync::Arc<std::sync::OnceLock<BTreeMap<(PointerBlock, u64), BTreeSet<ConditionTerm>>>>,
    /// True bitvector and int32-scaled pointer-offset equalities, indexed as
    /// an undirected adjacency graph whose edges retain one exact source
    /// proposition. Memory-load vertices use their
    /// assumption-free canonical snapshot spelling. Derived lazily from
    /// `condition_facts` and shared by unchanged clones.
    pub(super) bitvector_equality_facts: std::sync::Arc<
        std::sync::OnceLock<BTreeMap<Bitvector32Term, BTreeMap<Bitvector32Term, Proposition>>>,
    >,
    pub(super) prop_facts: std::sync::Arc<BTreeSet<Proposition>>,
    pub(super) resource_compositions: std::sync::Arc<BTreeSet<ResourceContext>>,
    pub(super) memory_loadable_facts: std::sync::Arc<BTreeMap<PointerBlock, BTreeSet<Proposition>>>,
    pub(super) memory_loadable_shape_facts:
        std::sync::Arc<std::sync::OnceLock<BTreeMap<(PointerBlock, u64), BTreeSet<Proposition>>>>,
    pub(super) memory_separation_facts: std::sync::Arc<
        BTreeMap<(PointerBlock, PointerBlock), Vec<(Proposition, CMemoryRange, CMemoryRange)>>,
    >,
    /// Same-block separation candidates projected from the compact resource
    /// compositions, keyed and maintained incrementally like
    /// `memory_separation_facts`. Two owned facts of one valid composition
    /// are separate by the composition law, so these entries carry the same
    /// authority the formerly materialized pair propositions did, without
    /// living in any ambient proposition set.
    pub(super) composition_separation_facts: std::sync::Arc<
        BTreeMap<(PointerBlock, PointerBlock), Vec<(Proposition, CMemoryRange, CMemoryRange)>>,
    >,
    pub(super) content_fingerprint: u64,
    pub(super) defer_non_exact_loadability_obligations: bool,
    pub(super) defer_non_exact_condition_reasoning: bool,
    pub(super) prefer_symbolic_external_loads: bool,
    pub(super) force_symbolic_external_loads: bool,
    pub(super) allow_symbolic_contract_loads: bool,
    pub(super) transport_memory_load_condition_facts: bool,
}

impl PartialEq for PureFactContext {
    fn eq(&self, other: &Self) -> bool {
        self.content_fingerprint == other.content_fingerprint
            && self.condition_facts == other.condition_facts
            && self.prop_facts == other.prop_facts
            && self.resource_compositions == other.resource_compositions
            && self.defer_non_exact_loadability_obligations
                == other.defer_non_exact_loadability_obligations
            && self.defer_non_exact_condition_reasoning == other.defer_non_exact_condition_reasoning
            && self.prefer_symbolic_external_loads == other.prefer_symbolic_external_loads
            && self.force_symbolic_external_loads == other.force_symbolic_external_loads
            && self.allow_symbolic_contract_loads == other.allow_symbolic_contract_loads
            && self.transport_memory_load_condition_facts
                == other.transport_memory_load_condition_facts
    }
}

impl Eq for PureFactContext {}

impl std::hash::Hash for PureFactContext {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.content_fingerprint);
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProofObligation {
    pub(super) proposition: Proposition,
    pub(super) context: Option<String>,
    pub(super) assumable: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ExecutionPureFact {
    pub(super) proposition: Proposition,
    pub(super) public: bool,
    pub(super) certified: bool,
    pub(super) certified_store: Option<CertifiedMemoryStore>,
    pub(super) transport: Option<CertifiedExecutionFactTransport>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CertifiedExecutionFactTransport {
    pub(super) source: Proposition,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) struct CertifiedMemoryStore {
    pub(super) before: CMemory,
    pub(super) after: CMemory,
    pub(super) pointer: Pointer,
    pub(super) value: CValue,
    pub(super) authorized_range: Option<CMemoryRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    pub(super) paths: Vec<SymbolicCExecutionPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

/// A complete function frontier produced from only the exact function's
/// contract entry state and requirements.
///
/// Unlike [`SymbolicCExecution`], this type is accepted as evidence when
/// certifying an opaque function rule. Its fields are kernel-private so callers
/// cannot turn an execution performed under arbitrary assumptions into
/// contract evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionContractExecution {
    pub(super) execution: SymbolicCExecution,
}

/// A kernel-created record of one exact whole-function execution judgment.
///
/// Callers may retain and present this artifact, but cannot manufacture or
/// alter its execution metadata. Contract certification revalidates the
/// boundary assumptions before reusing its checked frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CCheckedFunctionExecution {
    pub(super) state: CState,
    pub(super) function: CFunction,
    pub(super) arguments: Vec<CExpression>,
    pub(super) assumptions: PureFactContext,
    pub(super) environment: CExecutionEnvironment,
    pub(super) execution_semantics: CExecutionSemantics,
    pub(super) mode: CFunctionContractExecutionMode,
    pub(super) execution: SymbolicCExecution,
    /// Kernel-issued implications whose conclusions were added to the exact
    /// entry assumptions by an explicit proof certificate.
    pub(super) entry_derivations: Vec<Theorem>,
    /// Exact proof-selected evaluator prerequisites justified by
    /// `entry_derivations`.
    pub(super) entry_prerequisites: Vec<Proposition>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CFunctionContractExecutionMode {
    VerifyLoops,
    ExecuteLoops,
}

impl CFunctionContractExecution {
    pub fn path_count(&self) -> usize {
        self.execution.paths.len()
    }

    pub fn limit(&self) -> Option<&ExecutionLimit> {
        self.execution.limit.as_ref()
    }
}

impl CCheckedFunctionExecution {
    pub fn paths(&self) -> &[SymbolicCExecutionPath] {
        self.execution.paths()
    }

    pub fn limit(&self) -> Option<ExecutionLimit> {
        self.execution.limit()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    pub(super) assumptions: PureFactContext,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) effect_facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

/// An untrusted collection of replayed function outcomes.
///
/// Candidates deliberately carry no [`Theorem`]. They become useful as proof
/// evidence only after a checked kernel execution independently reproduces the
/// same complete path frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionExecutionCandidates {
    pub(super) state: CState,
    pub(super) function: CFunction,
    pub(super) arguments: Vec<CExpression>,
    pub(super) paths: Vec<CFunctionExecutionCandidate>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CFunctionExecutionCandidate {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) effect_facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCConditionEvaluation {
    pub(super) paths: Vec<SymbolicCConditionEvaluationPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCConditionEvaluationPath {
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CExpressionPath {
    pub(super) outcome: CExpressionOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CLValuePath {
    pub(super) outcome: CLValueOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CStatementExecutionPath {
    pub(super) outcome: CStatementOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CFunctionPath {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CArgumentsPath {
    pub(super) values: Vec<CValue>,
    pub(super) outcome: Option<CFunctionOutcome>,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct VerificationVariableGenerator {
    pub(super) next: u64,
    reserved: BTreeSet<Variable>,
}

impl VerificationVariableGenerator {
    /// Build the deterministic fresh-name stream used by both planning and
    /// certificate replay. Given the same lower bound and reserved set, the
    /// first available identifier and every successor are identical; callers
    /// carry `next` across proof steps so a replay never relies on accidental
    /// equality with an independently chosen symbolic name.
    pub(super) fn fresh_for(lower_bound: u64, existing: BTreeSet<Variable>) -> Self {
        Self {
            next: lower_bound,
            reserved: existing,
        }
    }

    pub(super) fn next(&mut self) -> Variable {
        let start = self.next;
        loop {
            let variable = Variable(self.next);
            self.next = self.next.wrapping_add(1);
            if self.reserved.insert(variable) {
                return variable;
            }
            assert!(
                self.next != start,
                "all symbolic variable identifiers are already reserved"
            );
        }
    }
}
