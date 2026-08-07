use super::api::{int32, normalize_exact_memory_loads_in_pointer_offset, uint8};
use super::reasoning::{
    bitvector_terms_proven_equal_for_memory_resolution,
    c_values_proven_equal_for_memory_resolution, collect_or_cases, instantiate_range_fold_step,
    int32_element_index_from_offset, memory_snapshots_proven_equal_at_pointer,
    pointers_proven_distinct_for_memory_resolution, pointers_proven_equal_for_memory_resolution,
    resource_context_has_read, signed_bitvector_constant, signed_i64_bitvector_constant,
};
use std::collections::{BTreeMap, BTreeSet};

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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CCompositeResourceDefinition {
    pub(super) name: String,
    pub(super) parameters: Vec<CParameter>,
    pub(super) condition: Option<SpecProposition>,
    pub(super) recursive: bool,
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
    pub(super) functions: BTreeMap<String, CFunction>,
    pub(super) verified_function_rules: BTreeMap<String, CVerifiedFunctionRule>,
    pub(super) verified_function_termination_rules:
        BTreeMap<String, CVerifiedFunctionTerminationRule>,
    pub(super) verified_loop_rules: Vec<CVerifiedLoopRule>,
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
    pub(super) required_assumptions: Assumptions,
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
    pub(super) bindings: BTreeMap<String, CLocalBinding>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(super) enum CLocalBinding {
    Object { value: CValue, c_type: CType },
    UninitializedObject { c_type: CType },
    ArrayObject { element_type: CType, length: u32 },
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemory {
    pub(super) blocks: BTreeMap<PointerBlock, CBlock>,
    pub(super) cells: BTreeMap<Pointer, CValue>,
    pub(super) heap: Box<CHeapMemory>,
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
    /// Indexed by arena id; `None` for entry states and for any snapshot
    /// whose first interning did not come from a recorded edge.
    derivations: Vec<Option<std::sync::Arc<CMemoryDerivation>>>,
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

/// Interns a memory snapshot in the thread-local arena. Structurally equal
/// snapshots interned on the same thread share one allocation and identity;
/// snapshots that cross threads still compare correctly through the content
/// hash and structural fallback.
pub fn intern_c_memory(memory: CMemory) -> SharedCMemory {
    C_MEMORY_ARENA.with(|(token, arena)| {
        let mut arena = arena.borrow_mut();
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
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceContext {
    pub(super) facts: Vec<CResourceFact>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceFact {
    Own(CResource),
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
        assumptions: &Assumptions,
    ) -> Option<ResourceContextValidityError>;

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &Assumptions,
    ) -> bool;

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<ResourceFactConsumption>;

    /// Returns one fact equivalent to composing this pair when the pair can be
    /// losslessly normalized. `None` leaves both facts in the resource state.
    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<CResourceFact>;

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact>;

    fn observable_facts(
        &self,
        facts: &[&CResourceFact],
        assumptions: &Assumptions,
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

impl ResourceFamily {
    const ALL: [Self; 3] = [Self::Memory, Self::Composite, Self::Token];
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Theorem {
    pub(super) proposition: Proposition,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum PropositionDerivationRule {
    ContextFree,
    ContextualAtomic {
        premises: Assumptions,
        premises_id: u64,
        for_simp: bool,
    },
    Explosion {
        premises: Assumptions,
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
        premises: Assumptions,
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

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Assumptions {
    pub(super) condition_facts: BTreeMap<ConditionTerm, bool>,
    pub(super) prop_facts: BTreeSet<Proposition>,
    pub(super) defer_non_exact_loadability_obligations: bool,
    pub(super) defer_non_exact_condition_reasoning: bool,
    pub(super) prefer_symbolic_external_loads: bool,
    pub(super) allow_symbolic_contract_loads: bool,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    pub(super) assumptions: Assumptions,
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

fn checked_signed_divide_const(left: u32, right: u32) -> Option<u32> {
    let left = left as i32;
    let right = right as i32;
    if right == 0 || (left == i32::MIN && right == -1) {
        None
    } else {
        Some((left / right) as u32)
    }
}

fn checked_signed_remainder_const(left: u32, right: u32) -> Option<u32> {
    let left = left as i32;
    let right = right as i32;
    if right == 0 || (left == i32::MIN && right == -1) {
        None
    } else {
        Some((left % right) as u32)
    }
}

fn checked_shift_count_const(count: u32) -> Option<u32> {
    let count = count as i32;
    (0..32).contains(&count).then_some(count as u32)
}

fn checked_signed_shift_left_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    let left = left as i32;
    if left < 0 {
        return None;
    }
    let shifted = (left as i64) << count;
    (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
}

fn checked_arithmetic_shift_right_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    Some(((left as i32) >> count) as u32)
}

fn signed_shift_left_overflows_const(left: u32, right: u32) -> Option<bool> {
    let count = checked_shift_count_const(right)?;
    let left = left as i32;
    if left < 0 {
        return Some(false);
    }
    Some(((left as i64) << count) > i64::from(i32::MAX))
}

impl Bitvector32Term {
    pub fn var(var: Variable) -> Self {
        Self::Variable(var)
    }

    pub fn constant(value: u32) -> Self {
        Self::Constant(value)
    }

    pub(crate) fn as_const(&self) -> Option<u32> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) | Self::MemoryLoad(_, _) | Self::PureFunctionApplication { .. } => {
                None
            }
            Self::Add(left, right) => Some(left.as_const()?.wrapping_add(right.as_const()?)),
            Self::Subtract(left, right) => Some(left.as_const()?.wrapping_sub(right.as_const()?)),
            Self::Multiply(left, right) => Some(left.as_const()?.wrapping_mul(right.as_const()?)),
            Self::Divide(left, right) => {
                checked_signed_divide_const(left.as_const()?, right.as_const()?)
            }
            Self::Remainder(left, right) => {
                checked_signed_remainder_const(left.as_const()?, right.as_const()?)
            }
            Self::ShiftLeft(left, right) => {
                checked_signed_shift_left_const(left.as_const()?, right.as_const()?)
            }
            Self::ArithmeticShiftRight(left, right) => {
                checked_arithmetic_shift_right_const(left.as_const()?, right.as_const()?)
            }
            Self::BitwiseAnd(left, right) => Some(left.as_const()? & right.as_const()?),
            Self::BitwiseOr(left, right) => Some(left.as_const()? | right.as_const()?),
            Self::BitwiseXor(left, right) => Some(left.as_const()? ^ right.as_const()?),
            Self::BitwiseNot(value) => Some(!value.as_const()?),
            Self::If {
                condition,
                then_term,
                else_term,
            } => match condition.as_ref() {
                ConditionTerm::Constant(true) => then_term.as_const(),
                ConditionTerm::Constant(false) => else_term.as_const(),
                _ => None,
            },
            Self::RangeFold { .. } => None,
        }
    }

    pub(super) fn subtract_one_base(&self) -> Option<Self> {
        match self {
            Self::Subtract(left, right) if right.as_ref() == &Self::Constant(1) => {
                Some(left.as_ref().clone())
            }
            _ => None,
        }
    }

    pub(super) fn is_subtract_one(&self) -> bool {
        self.subtract_one_base().is_some()
    }

    pub(super) fn add_const_base(&self, value: u32) -> Option<Self> {
        match self {
            Self::Add(left, right) if right.as_ref() == &Self::Constant(value) => {
                Some(left.as_ref().clone())
            }
            Self::Add(left, right) if left.as_ref() == &Self::Constant(value) => {
                Some(right.as_ref().clone())
            }
            _ => None,
        }
    }

    pub(super) fn add_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            Self::Add(left, right) => match (left.as_ref(), right.as_ref()) {
                (base, Self::Constant(value)) => Some((base.clone(), *value)),
                (Self::Constant(value), base) => Some((base.clone(), *value)),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn subtract_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            Self::Subtract(left, right) => match right.as_ref() {
                Self::Constant(value) => Some((left.as_ref().clone(), *value)),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn add(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                Self::Constant(left.wrapping_add(*right))
            }
            (_, Self::Subtract(base, subtrahend)) if subtrahend.as_ref() == &left => {
                base.as_ref().clone()
            }
            (Self::Subtract(base, subtrahend), _) if subtrahend.as_ref() == &right => {
                base.as_ref().clone()
            }
            (Self::Subtract(zero, subtrahend), Self::Add(base, addend))
                if zero.as_ref() == &Self::Constant(0) && subtrahend == base =>
            {
                addend.as_ref().clone()
            }
            (Self::Subtract(zero, subtrahend), Self::Add(addend, base))
                if zero.as_ref() == &Self::Constant(0) && subtrahend == base =>
            {
                addend.as_ref().clone()
            }
            (Self::Add(base, addend), Self::Subtract(zero, subtrahend))
                if zero.as_ref() == &Self::Constant(0) && base == subtrahend =>
            {
                addend.as_ref().clone()
            }
            (Self::Add(addend, base), Self::Subtract(zero, subtrahend))
                if zero.as_ref() == &Self::Constant(0) && base == subtrahend =>
            {
                addend.as_ref().clone()
            }
            (_, Self::Constant(0)) => left,
            (Self::Constant(0), _) => right,
            _ => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn subtract(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                Self::Constant(left.wrapping_sub(*right))
            }
            (_, Self::Constant(0)) => left,
            _ if left == right => Self::Constant(0),
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_base == right_base =>
            {
                Self::subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_base == right_addend =>
            {
                Self::subtract(left_addend.as_ref().clone(), right_base.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_addend == right_base =>
            {
                Self::subtract(left_base.as_ref().clone(), right_addend.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_addend == right_addend =>
            {
                Self::subtract(left_base.as_ref().clone(), right_base.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), _) if left_base.as_ref() == &right => {
                left_addend.as_ref().clone()
            }
            (Self::Add(left_base, left_addend), _) if left_addend.as_ref() == &right => {
                left_base.as_ref().clone()
            }
            (_, Self::Add(right_base, right_addend)) if &left == right_base.as_ref() => {
                Self::subtract(Self::Constant(0), right_addend.as_ref().clone())
            }
            (_, Self::Add(right_base, right_addend)) if &left == right_addend.as_ref() => {
                Self::subtract(Self::Constant(0), right_base.as_ref().clone())
            }
            _ => Self::Subtract(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn multiply(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                Self::Constant(left.wrapping_mul(*right))
            }
            (_, Self::Constant(1)) => left,
            (Self::Constant(1), _) => right,
            (_, Self::Constant(0)) | (Self::Constant(0), _) => Self::Constant(0),
            _ => Self::Multiply(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn divide(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_signed_divide_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::Divide(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(1)) => left,
            _ => Self::Divide(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn remainder(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_signed_remainder_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::Remainder(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            _ => Self::Remainder(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn shift_left(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_signed_shift_left_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::ShiftLeft(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            _ => Self::ShiftLeft(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn arithmetic_shift_right(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_arithmetic_shift_right_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::ArithmeticShiftRight(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(0)) => left,
            _ => Self::ArithmeticShiftRight(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn bitwise_and(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => Self::Constant(*left & *right),
            (_, Self::Constant(u32::MAX)) => left,
            (Self::Constant(u32::MAX), _) => right,
            (_, Self::Constant(0)) | (Self::Constant(0), _) => Self::Constant(0),
            _ if left == right => left,
            _ => Self::BitwiseAnd(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn bitwise_or(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => Self::Constant(*left | *right),
            (_, Self::Constant(0)) => left,
            (Self::Constant(0), _) => right,
            (_, Self::Constant(u32::MAX)) | (Self::Constant(u32::MAX), _) => {
                Self::Constant(u32::MAX)
            }
            _ if left == right => left,
            _ => Self::BitwiseOr(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn bitwise_xor(left: Self, right: Self) -> Self {
        fn flatten(term: Bitvector32Term, constant: &mut u32, terms: &mut Vec<Bitvector32Term>) {
            match term {
                Bitvector32Term::Constant(value) => *constant ^= value,
                Bitvector32Term::BitwiseXor(left, right) => {
                    flatten(*left, constant, terms);
                    flatten(*right, constant, terms);
                }
                term => terms.push(term),
            }
        }

        let mut constant = 0;
        let mut terms = Vec::new();
        flatten(left, &mut constant, &mut terms);
        flatten(right, &mut constant, &mut terms);
        terms.sort();

        let mut normalized = Vec::new();
        let mut index = 0;
        while index < terms.len() {
            let mut end = index + 1;
            while end < terms.len() && terms[end] == terms[index] {
                end += 1;
            }
            if (end - index) % 2 == 1 {
                normalized.push(terms[index].clone());
            }
            index = end;
        }
        if constant != 0 {
            normalized.push(Self::Constant(constant));
            normalized.sort();
        }

        normalized
            .into_iter()
            .reduce(|left, right| Self::BitwiseXor(Box::new(left), Box::new(right)))
            .unwrap_or(Self::Constant(0))
    }

    pub(super) fn bitwise_not(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::Constant(!value),
            Self::BitwiseNot(inner) => *inner,
            value => Self::BitwiseNot(Box::new(value)),
        }
    }

    pub fn if_then_else(condition: ConditionTerm, then_term: Self, else_term: Self) -> Self {
        match condition {
            ConditionTerm::Constant(true) => then_term,
            ConditionTerm::Constant(false) => else_term,
            _ if then_term == else_term => then_term,
            condition => Self::If {
                condition: Box::new(condition),
                then_term: Box::new(then_term),
                else_term: Box::new(else_term),
            },
        }
    }

    pub fn range_fold(
        start: Self,
        end: Self,
        initial: Self,
        accumulator: Variable,
        item: Variable,
        body: Self,
    ) -> Self {
        if start == end {
            return initial;
        }

        if Self::add(start.clone(), Self::Constant(1)) == end {
            return instantiate_range_fold_step(&body, accumulator, &initial, item, &start);
        }

        if let (Some(start_value), Some(end_value)) = (
            signed_bitvector_constant(&start),
            signed_bitvector_constant(&end),
        ) {
            let length = end_value - start_value;
            if length <= 0 {
                return initial;
            }
            if length <= RANGE_FOLD_CONCRETE_UNROLL_LIMIT {
                let mut value = initial;
                for index in start_value..end_value {
                    value = instantiate_range_fold_step(
                        &body,
                        accumulator,
                        &value,
                        item,
                        &signed_i64_bitvector_constant(index),
                    );
                }
                return value;
            }
        }

        Self::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        }
    }
}

impl PointerOffsetTerm {
    pub fn constant(value: i64) -> Self {
        Self::Constant(value)
    }

    pub(super) fn as_const(&self) -> Option<i64> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) => None,
            Self::Add(left, right) => left.as_const()?.checked_add(right.as_const()?),
            Self::Int32Scaled { value, byte_width } => {
                let value = value.as_const()? as i32 as i64;
                value.checked_mul(*byte_width)
            }
        }
    }

    pub(super) fn add(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left + right),
            (Some(0), _) => right,
            (_, Some(0)) => left,
            _ => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn scale_int32(value: Bitvector32Term, byte_width: i64) -> Self {
        match value.as_const() {
            Some(value) => Self::Constant((value as i32 as i64) * byte_width),
            None => Self::Int32Scaled {
                value: Box::new(value),
                byte_width,
            },
        }
    }
}

impl ConditionTerm {
    pub(super) fn signed_less_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) < (right as i32)),
            _ => Self::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) <= (right as i32)),
            _ => Self::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) > (right as i32)),
            _ => Self::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) >= (right as i32)),
            _ => Self::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::Bitvector32Equal(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_add_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_add(right as i32).1)
            }
            _ => Self::Bitvector32SignedAddOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_subtract_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_sub(right as i32).1)
            }
            _ => Self::Bitvector32SignedSubtractOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_multiply_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_mul(right as i32).1)
            }
            _ => Self::Bitvector32SignedMultiplyOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_divide_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(left == i32::MIN as u32 && right == (-1i32) as u32)
            }
            _ => Self::Bitvector32SignedDivideOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn signed_shift_left_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(signed_shift_left_overflows_const(left, right).unwrap_or(false))
            }
            _ => Self::Bitvector32SignedShiftLeftOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(super) fn pointer_offset_equal(left: PointerOffsetTerm, right: PointerOffsetTerm) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::PointerOffsetEqual(Box::new(left), Box::new(right)),
        }
    }

    pub fn pointer_equal(left: Pointer, right: Pointer) -> Self {
        if left == right {
            Self::Constant(true)
        } else if left.blocks_proven_distinct(&right) {
            Self::Constant(false)
        } else if left.block == right.block {
            Self::pointer_offset_equal(left.offset, right.offset)
        } else {
            Self::PointerEqual(Box::new(left), Box::new(right))
        }
    }
}

impl CType {
    pub(super) fn accepts(self, value: &CValue) -> bool {
        matches!(
            (self, value),
            (Self::Void, CValue::Void)
                | (Self::Int32, CValue::Int32(_))
                | (Self::UInt8, CValue::UInt8(_))
                | (Self::Int32Pointer, CValue::Pointer(_))
                | (Self::UInt8Pointer, CValue::Pointer(_))
        )
    }

    pub fn byte_width(self) -> u32 {
        match self {
            Self::Void => 0,
            Self::Int32 => 4,
            Self::UInt8 => 1,
            Self::Int32Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int32Array(length) => length.saturating_mul(4),
            Self::UInt8Array(length) => length,
        }
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::Int32Pointer => Some(Self::Int32),
            Self::UInt8Pointer => Some(Self::UInt8),
            _ => None,
        }
    }
}

impl CValue {
    pub(super) fn c_type(&self) -> CType {
        match self {
            Self::Void => CType::Void,
            Self::Int32(_) => CType::Int32,
            Self::UInt8(_) => CType::UInt8,
            Self::Pointer(_) => CType::Int32Pointer,
        }
    }

    pub(super) fn byte_width(&self) -> u32 {
        match self {
            Self::Void => 0,
            Self::Int32(_) => 4,
            Self::UInt8(_) => 1,
            Self::Pointer(_) => C_POINTER_BYTE_WIDTH,
        }
    }
}

impl CLValue {
    pub(super) fn local(name: impl Into<String>, value_type: CType) -> Self {
        Self {
            storage: CLValueStorage::Local { name: name.into() },
            value_type,
        }
    }

    pub(super) fn memory(pointer: Pointer, value_type: CType) -> Self {
        Self {
            storage: CLValueStorage::Memory { pointer },
            value_type,
        }
    }

    pub fn value_type(&self) -> CType {
        self.value_type
    }

    pub(super) fn pointer(&self, state: &CState) -> Option<Pointer> {
        match &self.storage {
            CLValueStorage::Local { name } => {
                let pointer = CMemory::local_pointer(name);
                state.memory.has_block(&pointer.block).then_some(pointer)
            }
            CLValueStorage::Memory { pointer } => Some(pointer.clone()),
        }
    }
}

impl Pointer {
    pub(crate) fn null() -> Self {
        Self {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn symbolic(variable: Variable) -> Self {
        Self {
            block: PointerBlock::Symbolic(variable),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) fn has_symbolic_block(&self) -> bool {
        matches!(
            self.block,
            PointerBlock::ExternalArgument | PointerBlock::Symbolic(_)
        )
    }

    pub(super) fn blocks_proven_distinct(&self, other: &Self) -> bool {
        self.block != other.block
            && (matches!(self.block, PointerBlock::Heap(_))
                || matches!(other.block, PointerBlock::Heap(_))
                || matches!(
                    (&self.block, &other.block),
                    (PointerBlock::Concrete(left), PointerBlock::Concrete(right)) if left != right
                ))
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) fn offset_by_int32_elements(&self, elements: Bitvector32Term) -> Self {
        self.offset_by_elements(elements, 4)
    }

    pub(crate) fn offset_by_bytes(&self, bytes: u32) -> Self {
        Self {
            block: self.block.clone(),
            offset: PointerOffsetTerm::add(
                self.offset.clone(),
                PointerOffsetTerm::Constant(i64::from(bytes)),
            ),
        }
    }

    pub(super) fn offset_by_elements(&self, elements: Bitvector32Term, byte_width: u32) -> Self {
        Self {
            block: self.block.clone(),
            offset: PointerOffsetTerm::add(
                self.offset.clone(),
                PointerOffsetTerm::scale_int32(elements, i64::from(byte_width)),
            ),
        }
    }

    pub(crate) fn element_index_from_base(&self, base: &Self) -> Option<Bitvector32Term> {
        if self.block != base.block {
            return None;
        }

        if self.offset == base.offset {
            return Some(Bitvector32Term::Constant(0));
        }

        if base.offset == PointerOffsetTerm::Constant(0) {
            return int32_element_index_from_offset(&self.offset);
        }

        match &self.offset {
            PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
                int32_element_index_from_offset(right)
            }
            PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
                int32_element_index_from_offset(left)
            }
            _ => {
                if let (Some(pointer_index), Some(base_index)) = (
                    int32_element_index_from_offset(&self.offset),
                    int32_element_index_from_offset(&base.offset),
                ) {
                    Some(Bitvector32Term::subtract(pointer_index, base_index))
                } else {
                    None
                }
            }
        }
    }
}

impl CParameter {
    pub fn new(name: impl Into<String>, c_type: CType) -> Self {
        Self {
            name: name.into(),
            c_type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }
}

impl CFunction {
    pub fn new(
        return_type: CType,
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        body: CStatement,
    ) -> Self {
        Self {
            return_type,
            name: name.into(),
            parameters,
            source_body: body.clone(),
            body,
            resource_requires: Vec::new(),
            resource_ensures: Vec::new(),
            contract_requires: Vec::new(),
            contract_ensures: Vec::new(),
            contract_mutable: Vec::new(),
            contract_claims: Vec::new(),
            opaque_contract_supported: true,
            composite_resource_definitions: Vec::new(),
        }
    }

    pub fn with_source_body(mut self, source_body: CStatement) -> Self {
        self.source_body = source_body;
        self
    }

    pub fn with_resource_summary(
        mut self,
        requires: Vec<CResourceSpec>,
        ensures: Vec<CResourceSpec>,
    ) -> Self {
        self.resource_requires = requires;
        self.resource_ensures = ensures;
        self
    }

    pub fn with_contract(
        mut self,
        requires: Vec<SpecProposition>,
        ensures: Vec<SpecProposition>,
        mutable: Vec<CMemorySegment>,
        claims: Vec<CFunctionContractClaim>,
        opaque_supported: bool,
    ) -> Self {
        self.contract_requires = requires;
        self.contract_ensures = ensures;
        self.contract_mutable = mutable;
        self.contract_claims = claims;
        self.opaque_contract_supported = opaque_supported;
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        definitions: Vec<CCompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions = definitions;
        self
    }

    pub fn return_type(&self) -> CType {
        self.return_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub fn body(&self) -> &CStatement {
        &self.body
    }

    pub fn source_body(&self) -> &CStatement {
        &self.source_body
    }

    pub fn resource_requires(&self) -> &[CResourceSpec] {
        &self.resource_requires
    }

    pub fn resource_ensures(&self) -> &[CResourceSpec] {
        &self.resource_ensures
    }

    pub fn contract_requires(&self) -> &[SpecProposition] {
        &self.contract_requires
    }

    pub fn contract_ensures(&self) -> &[SpecProposition] {
        &self.contract_ensures
    }

    pub fn contract_mutable(&self) -> &[CMemorySegment] {
        &self.contract_mutable
    }

    pub fn contract_claims(&self) -> &[CFunctionContractClaim] {
        &self.contract_claims
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.opaque_contract_supported
    }

    pub fn composite_resource_definitions(&self) -> &[CCompositeResourceDefinition] {
        &self.composite_resource_definitions
    }
}

impl CCompositeResourceDefinition {
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        recursive: bool,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            condition,
            recursive,
            contains,
            facts,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub fn condition(&self) -> Option<&SpecProposition> {
        self.condition.as_ref()
    }

    pub fn is_recursive(&self) -> bool {
        self.recursive
    }

    pub fn contains(&self) -> &[CResourceSpec] {
        &self.contains
    }

    pub fn facts(&self) -> &[SpecProposition] {
        &self.facts
    }
}

impl CFunctionContractClaim {
    pub fn body_safety() -> Self {
        Self {
            key: CFunctionContractClaimKey::BodySafety,
            target: CFunctionContractClaimTarget::BodySafety,
        }
    }

    pub fn effect(index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Effect(index),
            target: CFunctionContractClaimTarget::Effect,
        }
    }

    pub fn ensure_proposition(source_index: usize, contract_index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Ensure(source_index),
            target: CFunctionContractClaimTarget::EnsureProposition(contract_index),
        }
    }

    pub fn ensure_resource(source_index: usize, resource_index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Ensure(source_index),
            target: CFunctionContractClaimTarget::EnsureResource(resource_index),
        }
    }

    pub fn key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }

    pub fn target(&self) -> &CFunctionContractClaimTarget {
        &self.target
    }
}

impl CLoopInvariantCheck {
    pub fn new(
        proposition: SpecProposition,
        entry_context: Option<String>,
        preservation_context: Option<String>,
    ) -> Self {
        Self {
            proposition,
            entry_context,
            preservation_context,
        }
    }

    pub fn proposition(&self) -> &SpecProposition {
        &self.proposition
    }

    pub fn entry_context(&self) -> Option<&str> {
        self.entry_context.as_deref()
    }

    pub fn preservation_context(&self) -> Option<&str> {
        self.preservation_context.as_deref()
    }
}

impl CLoopEffectCheck {
    pub fn new(effect: CLoopEffect, context: Option<String>) -> Self {
        Self {
            effect,
            span: CLoopEffectSpan::Step,
            context,
        }
    }

    pub fn new_with_span(
        effect: CLoopEffect,
        span: CLoopEffectSpan,
        context: Option<String>,
    ) -> Self {
        Self {
            effect,
            span,
            context,
        }
    }

    pub fn effect(&self) -> &CLoopEffect {
        &self.effect
    }

    pub fn span(&self) -> CLoopEffectSpan {
        self.span
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }
}

impl CMemorySegment {
    pub fn new(base: CExpression, start: CExpression, end: CExpression) -> Self {
        Self {
            base,
            start,
            end,
            guard: None,
        }
    }

    pub fn with_guard(mut self, guard: SpecProposition) -> Self {
        self.guard = Some(guard);
        self
    }

    pub fn guard(&self) -> Option<&SpecProposition> {
        self.guard.as_ref()
    }
}

impl CMemoryRange {
    pub fn new(base: Pointer, start: Bitvector32Term, end: Bitvector32Term) -> Self {
        Self { base, start, end }
    }

    pub fn base(&self) -> &Pointer {
        &self.base
    }

    pub fn start(&self) -> &Bitvector32Term {
        &self.start
    }

    pub fn end(&self) -> &Bitvector32Term {
        &self.end
    }
}

impl CFunctionSpecification {
    pub fn new(
        state: CState,
        arguments: Vec<CExpression>,
        requires: Vec<Proposition>,
        outcome: CFunctionOutcome,
    ) -> Self {
        Self {
            state,
            arguments,
            requires,
            outcome,
        }
    }

    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn arguments(&self) -> &[CExpression] {
        &self.arguments
    }

    pub fn requires(&self) -> &[Proposition] {
        &self.requires
    }

    pub fn outcome(&self) -> &CFunctionOutcome {
        &self.outcome
    }
}

impl CExecutionEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function(mut self, function: CFunction) -> Self {
        self.functions.insert(function.name().to_string(), function);
        self
    }

    pub fn get_function(&self, name: &str) -> Option<&CFunction> {
        self.functions.get(name)
    }

    pub fn with_verified_function_rule(mut self, rule: CVerifiedFunctionRule) -> Self {
        self.verified_function_rules
            .insert(rule.function.name().to_string(), rule);
        self
    }

    pub fn with_verified_function_termination_rules(
        mut self,
        rules: impl IntoIterator<Item = CVerifiedFunctionTerminationRule>,
    ) -> Self {
        for rule in rules {
            self.verified_function_termination_rules
                .insert(rule.function.name().to_string(), rule);
        }
        self
    }

    pub fn has_verified_function_termination(&self, name: &str) -> bool {
        self.verified_function_termination_rules.contains_key(name)
    }

    pub fn without_verified_function_rule(mut self, name: &str) -> Self {
        self.verified_function_rules.remove(name);
        self
    }

    pub(super) fn get_verified_function_rule(&self, name: &str) -> Option<&CVerifiedFunctionRule> {
        self.verified_function_rules.get(name)
    }

    pub(crate) fn verified_function_rules(&self) -> Vec<CVerifiedFunctionRule> {
        self.verified_function_rules.values().cloned().collect()
    }

    pub fn with_verified_loop_rules(
        mut self,
        rules: impl IntoIterator<Item = CVerifiedLoopRule>,
    ) -> Self {
        self.verified_loop_rules.extend(rules);
        self
    }

    pub(super) fn applicable_verified_loop_rule(
        &self,
        state: &CState,
        statement: &CStatement,
        assumptions: &Assumptions,
    ) -> Option<&CVerifiedLoopRule> {
        self.verified_loop_rules.iter().find(|rule| {
            let statement_matches = rule.loop_statement == *statement;
            let assumptions_match = rule
                .required_assumptions
                .pure_facts()
                .iter()
                .all(|required| {
                    assumptions.pure_facts().contains(required)
                        || assumptions.proves(required)
                        || match required {
                            Proposition::CMemoryLoadable {
                                memory,
                                base,
                                bytes,
                            } => {
                                memory_snapshots_proven_equal_at_pointer(
                                    memory,
                                    state.memory(),
                                    base,
                                    assumptions,
                                ) && (bytes.as_const().is_some_and(|bytes| {
                                    resource_context_has_read(
                                        state.resources(),
                                        base,
                                        bytes,
                                        assumptions,
                                    )
                                }) || resource_context_has_symbolic_int32_range_read(
                                    state.resources(),
                                    base,
                                    bytes,
                                ))
                            }
                            _ => false,
                        }
                });
            let state_matches = rule.symbolic_entry_state.locals == state.locals
                && rule.symbolic_entry_state.memory == state.memory
                && super::api::resource_contexts_definitionally_equal_with_definitions(
                    &rule.composite_resource_definitions,
                    rule.symbolic_entry_state.memory(),
                    rule.symbolic_entry_state.resources(),
                    state.memory(),
                    state.resources(),
                    assumptions,
                );
            state_matches && statement_matches && assumptions_match
        })
    }
}

impl CVerifiedLoopRule {
    pub fn with_composite_resource_definitions(
        mut self,
        definitions: impl IntoIterator<Item = CCompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions.extend(definitions);
        self
    }
}

impl CTerminationError {
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for CTerminationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(formatter)
    }
}

impl std::error::Error for CTerminationError {}

fn resource_context_has_symbolic_int32_range_read(
    resources: &ResourceContext,
    base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    resources.facts().iter().any(|fact| {
        let Some(range) = fact.memory_range() else {
            return false;
        };
        let range_base = range.base().offset_by_int32_elements(range.start().clone());
        let range_bytes = Bitvector32Term::multiply(
            Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
            Bitvector32Term::Constant(4),
        );
        &range_base == base && &range_bytes == bytes
    })
}

impl CLocalEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.set(name, value);
        self
    }

    pub fn with_typed(mut self, name: impl Into<String>, value: CValue, c_type: CType) -> Self {
        self.set_typed(name, value, c_type);
        self
    }

    pub fn with_int32_array(mut self, name: impl Into<String>, length: u32) -> Self {
        self.set_int32_array(name, length);
        self
    }

    pub fn set(&mut self, name: impl Into<String>, value: CValue) {
        let c_type = value.c_type();
        self.set_typed(name, value, c_type);
    }

    pub fn set_typed(&mut self, name: impl Into<String>, value: CValue, c_type: CType) {
        self.bindings
            .insert(name.into(), CLocalBinding::Object { value, c_type });
    }

    pub(super) fn set_uninitialized(&mut self, name: impl Into<String>, c_type: CType) {
        self.bindings
            .insert(name.into(), CLocalBinding::UninitializedObject { c_type });
    }

    pub fn set_int32_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int32, length);
    }

    pub fn set_uint8_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::UInt8, length);
    }

    pub(super) fn set_array_object(
        &mut self,
        name: impl Into<String>,
        element_type: CType,
        length: u32,
    ) {
        self.bindings.insert(
            name.into(),
            CLocalBinding::ArrayObject {
                element_type,
                length,
            },
        );
    }

    pub fn get(&self, name: &str) -> Option<&CValue> {
        match self.bindings.get(name) {
            Some(CLocalBinding::Object { value, .. }) => Some(value),
            Some(CLocalBinding::UninitializedObject { .. })
            | Some(CLocalBinding::ArrayObject { .. })
            | None => None,
        }
    }

    pub fn object_values(&self) -> impl Iterator<Item = (&str, &CValue)> {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::Object { value, .. } => Some((name.as_str(), value)),
                CLocalBinding::UninitializedObject { .. } | CLocalBinding::ArrayObject { .. } => {
                    None
                }
            })
    }

    pub fn array_object_values(&self) -> impl Iterator<Item = (&str, CValue, CType)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::ArrayObject { element_type, .. } => Some((
                    name.as_str(),
                    CValue::Pointer(CMemory::local_pointer(name)),
                    *element_type,
                )),
                CLocalBinding::Object { .. } | CLocalBinding::UninitializedObject { .. } => None,
            })
    }

    pub(super) fn object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
        }
    }

    pub(super) fn scalar_object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { .. }) | None => None,
        }
    }

    pub(super) fn binding(&self, name: &str) -> Option<&CLocalBinding> {
        self.bindings.get(name)
    }

    pub(super) fn is_array_object(&self, name: &str) -> bool {
        matches!(self.binding(name), Some(CLocalBinding::ArrayObject { .. }))
    }
}

impl CBlock {
    pub fn new(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
        }
    }

    pub(super) fn with_symbolic_size(size: Bitvector32Term) -> Self {
        Self { size }
    }

    pub fn size(&self) -> &Bitvector32Term {
        &self.size
    }
}

fn heap_allocation_may_contain_pointer(base: &Pointer, pointer: &Pointer) -> bool {
    if base.block != pointer.block {
        return false;
    }
    if base.block != PointerBlock::ExternalArgument {
        return true;
    }

    if pointer.offset == base.offset {
        return true;
    }

    fn contains_base_offset(term: &PointerOffsetTerm, base: &PointerOffsetTerm) -> bool {
        match term {
            PointerOffsetTerm::Add(left, right) => {
                left.as_ref() == base
                    || right.as_ref() == base
                    || contains_base_offset(left, base)
                    || contains_base_offset(right, base)
            }
            PointerOffsetTerm::Constant(_)
            | PointerOffsetTerm::Variable(_)
            | PointerOffsetTerm::Int32Scaled { .. } => false,
        }
    }

    contains_base_offset(&pointer.offset, &base.offset)
}

impl CMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn has_same_snapshot_markers(&self, other: &Self) -> bool {
        self.blocks == other.blocks && self.heap == other.heap
    }

    pub fn with_block(mut self, block: impl Into<PointerBlock>, size: u32) -> Self {
        let block = block.into();
        // Havoc marker blocks mean "the state may have changed", never "a
        // fresh block appeared"; recording a benign block-declaration edge
        // for one would launder the havoc (conventions.md's soundness trap,
        // pinned by `conditions_equal_modulo_proven_snapshots_needs_frame_
        // evidence`). The havoc producers insert their markers directly,
        // but tests and any future caller may spell them through this
        // constructor, so the refusal lives here.
        if memory_dag_disabled() || block.starts_with("havoc:") || block.starts_with("call-havoc:")
        {
            self.blocks.insert(block, CBlock::new(size));
            return self;
        }
        let base = intern_c_memory_ref(&self);
        self.blocks.insert(block.clone(), CBlock::new(size));
        record_c_memory_derivation(&self, CMemoryDerivation::BlockDeclared { base, block });
        self
    }

    pub(super) fn free_heap_block(mut self, pointer: &Pointer) -> Result<Self, CInvalidFree> {
        if self.heap.retired_allocations.contains_key(pointer) {
            return Err(CInvalidFree::DoubleFree);
        }
        let Some(bytes) = self.heap.live_allocations.remove(pointer) else {
            return Err(
                if self
                    .heap
                    .live_allocations
                    .keys()
                    .any(|base| heap_allocation_may_contain_pointer(base, pointer))
                {
                    CInvalidFree::InteriorPointer
                } else {
                    CInvalidFree::NonHeapPointer
                },
            );
        };
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        if pointer.block != PointerBlock::ExternalArgument {
            self.blocks.remove(&pointer.block);
        }
        self.heap
            .retired_allocations
            .insert(pointer.clone(), bytes.clone());
        self.heap.uninitialized_allocations.remove(pointer);
        self.cells
            .retain(|cell, _| !heap_allocation_may_contain_pointer(pointer, cell));
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::HeapFreed {
                    base,
                    allocation_base: pointer.clone(),
                    bytes: bytes.clone(),
                },
            );
        }
        Ok(self)
    }

    pub(super) fn live_heap_block_size(&self, pointer: &Pointer) -> Option<&Bitvector32Term> {
        self.heap.live_allocations.get(pointer)
    }

    pub(crate) fn is_live_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .live_allocations
            .keys()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
    }

    pub(super) fn is_uninitialized_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .uninitialized_allocations
            .iter()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
    }

    pub(super) fn is_retired_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .retired_allocations
            .keys()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
    }

    /// Registers the exact base named by an allocation contract. Unlike a
    /// fresh `malloc`, this does not create a concrete block or imply that its
    /// existing bytes are uninitialized; access remains governed by the
    /// accompanying memory resources.
    pub(super) fn with_heap_allocation_claim(
        mut self,
        base: Pointer,
        bytes: impl Into<Bitvector32Term>,
    ) -> Option<Self> {
        let bytes = bytes.into();
        if bytes.as_const() == Some(0) || self.heap.retired_allocations.contains_key(&base) {
            return None;
        }
        match self.heap.live_allocations.get(&base) {
            Some(existing) if existing != &bytes => None,
            Some(_) => Some(self),
            None => {
                self.heap.live_allocations.insert(base, bytes);
                Some(self)
            }
        }
    }

    pub(super) fn with_pending_heap_allocation(
        mut self,
        base: Pointer,
        bytes: Bitvector32Term,
    ) -> Self {
        let prior = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        self.heap
            .pending_allocations
            .insert(base.clone(), bytes.clone());
        if let Some(prior) = prior {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::HeapAllocationPending {
                    base: prior,
                    allocation_base: base,
                    bytes,
                },
            );
        }
        self
    }

    pub(super) fn has_pending_heap_allocation(&self) -> bool {
        !self.heap.pending_allocations.is_empty()
    }

    pub(super) fn heap_identity_in_use(&self, identity: u64) -> bool {
        self.blocks.contains_key(&PointerBlock::Heap(identity))
            || self
                .heap
                .retired_allocations
                .keys()
                .any(|base| base.block == PointerBlock::Heap(identity))
            || self
                .heap
                .pending_allocations
                .keys()
                .any(|base| base.block == PointerBlock::Symbolic(Variable(identity)))
    }

    pub(super) fn resolve_pending_heap_allocation(
        mut self,
        base: &Pointer,
        succeeds: bool,
    ) -> Option<(Self, Bitvector32Term, Pointer)> {
        let prior = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        let bytes = self.heap.pending_allocations.remove(base)?;
        let resolved_base = if succeeds {
            let PointerBlock::Symbolic(Variable(identity)) = base.block else {
                return None;
            };
            Pointer {
                block: PointerBlock::Heap(identity),
                offset: PointerOffsetTerm::Constant(0),
            }
        } else {
            Pointer::null()
        };
        if succeeds {
            self.blocks.insert(
                resolved_base.block.clone(),
                CBlock::with_symbolic_size(bytes.clone()),
            );
            self.heap
                .live_allocations
                .insert(resolved_base.clone(), bytes.clone());
            self.heap
                .uninitialized_allocations
                .insert(resolved_base.clone());
            if let Some(prior) = prior {
                record_c_memory_derivation(
                    &self,
                    CMemoryDerivation::HeapAllocated {
                        base: prior,
                        block: resolved_base.block.clone(),
                        bytes: bytes.clone(),
                    },
                );
            }
        }
        Some((self, bytes, resolved_base))
    }

    pub(super) fn with_loop_memory_havoc(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
    ) -> Self {
        // A loop body that may write memory can clobber, through some
        // pointer, any cell it can reach. Drop concrete cells outside the
        // preserved (scalar stack local) blocks so loop-head and post-loop
        // reads do not observe stale pre-loop values; anything that must
        // survive the loop has to be restated as a loop invariant. The
        // marker block additionally defeats symbolic cross-loop load
        // equality for the remaining symbolic memory.
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        self.cells
            .retain(|pointer, _| preserved_blocks.contains(&pointer.block));
        self.blocks
            .insert(format!("havoc:{}", variable.0).into(), CBlock::new(0));
        if let Some(base) = base {
            record_c_memory_derivation(&self, CMemoryDerivation::LoopHavoc { base, variable });
        }
        self
    }

    pub(super) fn with_call_memory_havoc(
        mut self,
        variable: Variable,
        mutable_ranges: &[CMemoryRange],
        assumptions: &Assumptions,
    ) -> Self {
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        self.cells.retain(|pointer, _| {
            pointer.block.starts_with("local:")
                || assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        self.blocks
            .insert(format!("call-havoc:{}", variable.0).into(), CBlock::new(0));
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::CallHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.to_vec(),
                },
            );
        }
        self
    }

    pub fn store(mut self, pointer: Pointer, value: CValue) -> Self {
        if memory_dag_disabled() {
            self.cells.insert(pointer, value);
            return self;
        }
        let base = intern_c_memory_ref(&self);
        self.cells.insert(pointer.clone(), value.clone());
        record_c_memory_derivation(
            &self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        self
    }

    pub fn load(&self, pointer: &Pointer) -> CExpressionOutcome {
        match self.cells.get(pointer) {
            Some(value) => CExpressionOutcome::Value(value.clone()),
            None => CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
        }
    }

    pub fn differing_cell_pointers(&self, other: &Self) -> Vec<Pointer> {
        let mut pointers = self.cells.keys().cloned().collect::<BTreeSet<_>>();
        pointers.extend(other.cells.keys().cloned());
        pointers
            .into_iter()
            .filter(|pointer| self.cells.get(pointer) != other.cells.get(pointer))
            .collect()
    }

    pub(super) fn known_value(&self, pointer: &Pointer) -> Option<CValue> {
        self.cells.get(pointer).cloned()
    }

    pub(super) fn without_cell(&self, pointer: &Pointer) -> Self {
        let mut memory = self.clone();
        memory.cells.remove(pointer);
        memory
    }

    pub(super) fn without_possible_aliasing_cells(
        &self,
        pointer: &Pointer,
        assumptions: &Assumptions,
    ) -> Self {
        let normalized_pointer = Pointer {
            block: pointer.block.clone(),
            offset: normalize_exact_memory_loads_in_pointer_offset(&pointer.offset, assumptions, 0),
        };
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(self));
        let mut memory = self.clone();
        memory.cells.retain(|cell_pointer, _| {
            let normalized_cell_pointer = Pointer {
                block: cell_pointer.block.clone(),
                offset: normalize_exact_memory_loads_in_pointer_offset(
                    &cell_pointer.offset,
                    assumptions,
                    0,
                ),
            };
            pointers_proven_distinct_for_memory_resolution(
                &normalized_cell_pointer,
                &normalized_pointer,
                assumptions,
            )
        });
        if let Some(base) = base {
            record_c_memory_derivation(&memory, CMemoryDerivation::CellsForgotten { base });
        }
        memory
    }

    pub(super) fn local_pointer(name: &str) -> Pointer {
        Pointer {
            block: format!("local:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn has_block(&self, block: &PointerBlock) -> bool {
        self.blocks.contains_key(block)
    }

    pub(super) fn is_loadable_concretely(&self, pointer: &Pointer, byte_width: u32) -> bool {
        self.cells
            .get(pointer)
            .is_some_and(|value| value.byte_width() == byte_width)
    }

    pub(super) fn can_store_concretely(&self, pointer: &Pointer, value: &CValue) -> bool {
        self.cells.contains_key(pointer) || self.access_in_bounds(pointer, value.byte_width())
    }

    pub(super) fn access_in_bounds(&self, pointer: &Pointer, byte_width: u32) -> bool {
        let Some(offset) = pointer.offset.as_const() else {
            return false;
        };
        let Ok(offset) = u32::try_from(offset) else {
            return false;
        };
        let Some(block) = self.blocks.get(&pointer.block) else {
            return false;
        };
        let Some(block_size) = block.size().as_const() else {
            return false;
        };
        offset
            .checked_add(byte_width)
            .is_some_and(|end| end <= block_size)
    }

    pub(super) fn symbolic_int32_load(&self, pointer: &Pointer) -> CValue {
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(super) fn symbolic_uint8_load(&self, pointer: &Pointer) -> CValue {
        uint8(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(super) fn symbolic_pointer_load(
        &self,
        pointer: &Pointer,
        pointee_byte_width: u32,
    ) -> CValue {
        CValue::Pointer(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(self.clone()),
                    Box::new(pointer.clone()),
                ),
                i64::from(pointee_byte_width),
            ),
        })
    }
}

impl CState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_local(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.locals.set(name, value);
        self
    }

    pub fn with_int32_array_local(mut self, name: impl Into<String>, length: u32) -> Self {
        self.locals.set_int32_array(name, length);
        self
    }

    pub fn with_memory(mut self, memory: CMemory) -> Self {
        self.memory = memory;
        self
    }

    pub fn with_resource_context(mut self, resources: ResourceContext) -> Self {
        self.resources = resources;
        self
    }

    pub fn locals(&self) -> &CLocalEnvironment {
        &self.locals
    }

    pub(crate) fn local_object_type(&self, name: &str) -> Option<CType> {
        self.locals.object_type(name)
    }

    pub fn memory(&self) -> &CMemory {
        &self.memory
    }

    pub fn resources(&self) -> &ResourceContext {
        &self.resources
    }
}

impl ResourceContext {
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a resource fact without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_fact` when proposition assumptions are
    /// available.
    pub fn unchecked_with_fact(mut self, fact: CResourceFact) -> Self {
        self.facts.push(fact);
        self
    }

    /// Adds resource facts without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_facts` when proposition assumptions are
    /// available.
    pub fn unchecked_with_facts(mut self, facts: impl IntoIterator<Item = CResourceFact>) -> Self {
        self.facts.extend(facts);
        self
    }

    pub fn try_compose_with_fact(
        self,
        fact: CResourceFact,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts(std::iter::once(fact), assumptions)
    }

    pub fn try_compose_with_facts(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_facts_delaying_normalization(facts, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(super) fn try_compose_with_facts_delaying_normalization(
        self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        let context = self.unchecked_with_facts(facts);
        if let Some(error) = context.validity_error(assumptions) {
            return Err(error);
        }
        Ok(context)
    }

    /// Extends a context whose validity has already been checked, validating
    /// only pairs that contain at least one newly added fact.
    pub(super) fn try_compose_into_valid_context_delaying_normalization(
        mut self,
        facts: impl IntoIterator<Item = CResourceFact>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        let first_new = self.facts.len();
        self.facts.extend(facts);
        for right_index in first_new..self.facts.len() {
            let right = &self.facts[right_index];
            for left in &self.facts[..right_index] {
                if left.family() != right.family() {
                    continue;
                }
                if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                    left,
                    right,
                    assumptions,
                ) {
                    return Err(error);
                }
            }
        }
        Ok(self)
    }

    pub fn facts(&self) -> &[CResourceFact] {
        &self.facts
    }

    pub fn validity_error(
        &self,
        assumptions: &Assumptions,
    ) -> Option<ResourceContextValidityError> {
        for i in 0..self.facts.len() {
            for right in &self.facts[i + 1..] {
                let left = &self.facts[i];
                if left.family() != right.family() {
                    continue;
                }
                if let Some(error) = resource_family_algebra(left.family()).pair_validity_error(
                    left,
                    right,
                    assumptions,
                ) {
                    return Some(error);
                }
            }
        }
        None
    }

    pub fn is_valid(&self, assumptions: &Assumptions) -> bool {
        self.validity_error(assumptions).is_none()
    }

    pub fn observable_facts(
        &self,
        assumptions: &Assumptions,
    ) -> Result<Vec<Proposition>, ResourceContextValidityError> {
        if let Some(error) = self.validity_error(assumptions) {
            return Err(error);
        }
        Ok(self.observable_facts_assuming_valid(assumptions))
    }

    /// Projects facts from a resource composition whose validity has already
    /// been established by an enclosing resource law.
    pub(crate) fn observable_facts_assuming_valid(
        &self,
        assumptions: &Assumptions,
    ) -> Vec<Proposition> {
        let mut propositions = Vec::new();
        for family in ResourceFamily::ALL {
            let facts = self
                .facts
                .iter()
                .filter(|fact| fact.family() == family)
                .collect::<Vec<_>>();
            propositions
                .extend(resource_family_algebra(family).observable_facts(&facts, assumptions));
        }
        propositions.extend(self.cross_family_separate_facts());
        propositions
    }

    fn cross_family_separate_facts(&self) -> Vec<Proposition> {
        let owned = self
            .facts
            .iter()
            .filter_map(CResourceFact::owned_resource)
            .collect::<Vec<_>>();
        let mut propositions = Vec::new();
        for i in 0..owned.len() {
            for right in &owned[i + 1..] {
                let left = owned[i];
                if left.family() == right.family() {
                    continue;
                }
                propositions.push(Proposition::CResourceSeparate {
                    left: (*left).clone(),
                    right: (**right).clone(),
                });
            }
        }
        propositions
    }

    pub fn satisfies_fact(&self, fact: &CResourceFact, assumptions: &Assumptions) -> bool {
        if self.facts.contains(fact) {
            return true;
        }
        if self
            .facts
            .iter()
            .any(|available| resource_fact_entails(available, fact, assumptions))
        {
            return true;
        }
        // A required fact may span several adjacent held resources; merge
        // them and retry once. Only memory resources have a split/merge
        // algebra: token and composite entailment is decided one fact at a
        // time above. Normalizing an unrelated ambient memory context while
        // looking for a missing token or composite makes an exact resource
        // query depend on every symbolic range the caller happens to hold.
        if fact.family() != ResourceFamily::Memory {
            return false;
        }
        let normalized = self.clone().normalized(assumptions);
        normalized.facts.len() < self.facts.len()
            && normalized
                .facts
                .iter()
                .any(|available| resource_fact_entails(available, fact, assumptions))
    }

    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    pub(super) fn permits_memory_read(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> bool {
        if self.permits_memory_read_structurally(pointer, byte_width, assumptions) {
            return true;
        }
        self.facts.iter().any(|resource| {
            memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
        })
    }

    pub(super) fn permits_memory_read_structurally(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> bool {
        for resource in &self.facts {
            let Some(range) = resource_fact_read_core_range(resource) else {
                continue;
            };
            if pointer_has_structural_range_base(pointer, range.base())
                && memory_resource_fact_permits_read(resource, pointer, byte_width, assumptions)
            {
                return true;
            }
        }
        false
    }

    pub(super) fn memory_write_range(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> Option<&CMemoryRange> {
        for resource in &self.facts {
            let CResourceFact::Own(CResource::Memory(range)) = resource else {
                continue;
            };
            if pointer_has_structural_range_base(pointer, range.base())
                && memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
            {
                return Some(range);
            }
        }
        self.facts.iter().find_map(|resource| {
            memory_resource_fact_permits_write(resource, pointer, byte_width, assumptions)
                .then(|| resource.memory_own_range())
                .flatten()
        })
    }

    pub fn without_fact(self, fact: &CResourceFact, assumptions: &Assumptions) -> Option<Self> {
        self.without_fact_delaying_normalization(fact, assumptions)
            .map(|context| context.normalized(assumptions))
    }

    pub(super) fn without_fact_delaying_normalization(
        mut self,
        fact: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<Self> {
        self.consume_fact_without_normalizing(fact, assumptions)
            .then_some(self)
    }

    pub(crate) fn without_exact_representation(mut self, fact: &CResourceFact) -> Option<Self> {
        let index = self.facts.iter().position(|available| available == fact)?;
        self.facts.remove(index);
        Some(self)
    }

    /// Consumes several facts while postponing whole-context normalization
    /// until the end. If a required fact is only available after adjacent
    /// resources are merged, normalize once at that point and retry it.
    pub fn without_facts(self, facts: &[CResourceFact], assumptions: &Assumptions) -> Option<Self> {
        let mut context = self;
        for fact in facts {
            if context.consume_fact_without_normalizing(fact, assumptions) {
                continue;
            }
            context = context.normalized(assumptions);
            if !context.consume_fact_without_normalizing(fact, assumptions) {
                return None;
            }
        }
        Some(context.normalized(assumptions))
    }

    fn consume_fact_without_normalizing(
        &mut self,
        fact: &CResourceFact,
        assumptions: &Assumptions,
    ) -> bool {
        let algebra = resource_family_algebra(fact.family());
        for index in 0..self.facts.len() {
            let available = &self.facts[index];
            if available.family() != fact.family() {
                continue;
            }
            let Some(consumption) = algebra.consume(available, fact, assumptions) else {
                continue;
            };
            if let ResourceFactConsumption::Replace(residual) = consumption {
                self.facts.remove(index);
                self.facts.extend(residual);
            }
            return true;
        }
        false
    }

    pub(super) fn normalized(mut self, assumptions: &Assumptions) -> Self {
        let mut i = 0;
        while i < self.facts.len() {
            let mut changed = false;
            let mut j = i + 1;
            while j < self.facts.len() {
                if let Some(merged) =
                    normalize_resource_fact_pair(&self.facts[i], &self.facts[j], assumptions)
                {
                    self.facts[i] = merged;
                    self.facts.remove(j);
                    changed = true;
                    break;
                }
                j += 1;
            }
            if changed {
                i = 0;
            } else {
                i += 1;
            }
        }
        self
    }
}

fn resource_family_algebra(family: ResourceFamily) -> &'static dyn ResourceFamilyAlgebra {
    let algebra: &'static dyn ResourceFamilyAlgebra = match family {
        ResourceFamily::Memory => &MEMORY_RESOURCE_ALGEBRA,
        ResourceFamily::Composite => &COMPOSITE_RESOURCE_ALGEBRA,
        ResourceFamily::Token => &TOKEN_RESOURCE_ALGEBRA,
    };
    debug_assert_eq!(algebra.family(), family);
    algebra
}

fn resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> bool {
    available.family() == required.family()
        && resource_family_algebra(available.family()).entails(available, required, assumptions)
}

fn normalize_resource_fact_pair(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<CResourceFact> {
    if left.family() != right.family() {
        return None;
    }
    resource_family_algebra(left.family()).normalize_pair(left, right, assumptions)
}

fn memory_resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> bool {
    if available == required {
        return true;
    }
    match (available, required) {
        (_, _) if required.memory_view_range().is_some() => {
            let required = required.memory_view_range().expect("checked above");
            let Some(available) = resource_fact_read_core_range(available) else {
                return false;
            };
            memory_range_covers(&available, required, assumptions)
        }
        (_, _) if required.memory_own_range().is_some() => {
            let Some(available) = available.memory_own_range() else {
                return false;
            };
            let required = required.memory_own_range().expect("checked above");
            memory_range_covers(available, required, assumptions)
        }
        _ => false,
    }
}

fn consume_memory_resource_fact(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<ResourceFactConsumption> {
    if let Some(required) = required.memory_view_range() {
        return resource_fact_read_core_range(available)
            .is_some_and(|available| memory_range_covers(&available, required, assumptions))
            .then_some(ResourceFactConsumption::Preserve);
    }
    if let Some(required) = required.memory_own_range() {
        let available = available.memory_own_range()?;
        if !memory_range_covers(available, required, assumptions) {
            return None;
        }
        return Some(ResourceFactConsumption::Replace(
            split_memory_range(available, required, assumptions)?
                .into_iter()
                .map(CResourceFact::own_memory)
                .collect(),
        ));
    }
    unreachable!("non-memory resource sent to memory resource consumer")
}

fn exact_resources_proven_equal(
    left: &CResource,
    right: &CResource,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| {
                        c_values_proven_equal_for_memory_resolution(left, right, assumptions)
                    })
        }
        _ => false,
    }
}

fn exact_resource_fact_entails(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> bool {
    match (available, required) {
        (CResourceFact::Own(available), CResourceFact::Own(required)) => {
            exact_resources_proven_equal(available, required, assumptions)
        }
        (
            CResourceFact::Own(available) | CResourceFact::View(available),
            CResourceFact::View(required),
        ) => exact_resources_proven_equal(available, required, assumptions),
        _ => false,
    }
}

fn consume_exact_resource_fact(
    available: &CResourceFact,
    required: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<ResourceFactConsumption> {
    if !exact_resource_fact_entails(available, required, assumptions) {
        return None;
    }
    Some(if required.is_view() {
        ResourceFactConsumption::Preserve
    } else {
        ResourceFactConsumption::Replace(Vec::new())
    })
}

fn combine_exact_resource_facts(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<CResourceFact> {
    match (left, right) {
        (CResourceFact::Own(left), CResourceFact::View(right))
        | (CResourceFact::View(right), CResourceFact::Own(left))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(CResourceFact::Own(left.clone()))
        }
        (CResourceFact::View(left), CResourceFact::View(right))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(CResourceFact::View(left.clone()))
        }
        _ => None,
    }
}

fn access_mode_core(resource: &CResourceFact) -> Option<CResourceFact> {
    match resource {
        CResourceFact::Own(resource) | CResourceFact::View(resource) => {
            Some(CResourceFact::View(resource.clone()))
        }
    }
}

fn exact_resource_pair_validity_error(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<ResourceContextValidityError> {
    match (left, right) {
        (CResourceFact::Own(left), CResourceFact::Own(right))
            if exact_resources_proven_equal(left, right, assumptions) =>
        {
            Some(ResourceContextValidityError::DuplicateOwnedResourceFact(
                CResourceFact::Own(left.clone()),
            ))
        }
        _ => None,
    }
}

fn same_family_separate_facts(facts: &[&CResourceFact]) -> Vec<Proposition> {
    let owned = facts
        .iter()
        .filter_map(|fact| fact.owned_resource())
        .collect::<Vec<_>>();
    let mut propositions = Vec::new();
    for i in 0..owned.len() {
        for right in &owned[i + 1..] {
            propositions.push(Proposition::CResourceSeparate {
                left: owned[i].clone(),
                right: (*right).clone(),
            });
        }
    }
    propositions
}

impl ResourceFamilyAlgebra for MemoryResourceAlgebra {
    fn family(&self) -> ResourceFamily {
        ResourceFamily::Memory
    }

    fn pair_validity_error(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<ResourceContextValidityError> {
        let (Some(left), Some(right)) = (left.memory_own_range(), right.memory_own_range()) else {
            return None;
        };
        memory_ranges_proven_overlapping(left, right, assumptions).then(|| {
            ResourceContextValidityError::OverlappingWriteResources {
                left: left.clone(),
                right: right.clone(),
            }
        })
    }

    fn entails(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &Assumptions,
    ) -> bool {
        memory_resource_fact_entails(available, required, assumptions)
    }

    fn consume(
        &self,
        available: &CResourceFact,
        required: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<ResourceFactConsumption> {
        consume_memory_resource_fact(available, required, assumptions)
    }

    fn normalize_pair(
        &self,
        left: &CResourceFact,
        right: &CResourceFact,
        assumptions: &Assumptions,
    ) -> Option<CResourceFact> {
        combine_memory_resource_facts(left, right, assumptions)
    }

    fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
        access_mode_core(fact)
    }

    fn observable_facts(
        &self,
        facts: &[&CResourceFact],
        _assumptions: &Assumptions,
    ) -> Vec<Proposition> {
        same_family_separate_facts(facts)
    }
}

macro_rules! impl_exact_resource_algebra {
    ($algebra:ty, $family:expr) => {
        impl ResourceFamilyAlgebra for $algebra {
            fn family(&self) -> ResourceFamily {
                $family
            }

            fn pair_validity_error(
                &self,
                left: &CResourceFact,
                right: &CResourceFact,
                assumptions: &Assumptions,
            ) -> Option<ResourceContextValidityError> {
                exact_resource_pair_validity_error(left, right, assumptions)
            }

            fn entails(
                &self,
                available: &CResourceFact,
                required: &CResourceFact,
                assumptions: &Assumptions,
            ) -> bool {
                exact_resource_fact_entails(available, required, assumptions)
            }

            fn consume(
                &self,
                available: &CResourceFact,
                required: &CResourceFact,
                assumptions: &Assumptions,
            ) -> Option<ResourceFactConsumption> {
                consume_exact_resource_fact(available, required, assumptions)
            }

            fn normalize_pair(
                &self,
                left: &CResourceFact,
                right: &CResourceFact,
                assumptions: &Assumptions,
            ) -> Option<CResourceFact> {
                combine_exact_resource_facts(left, right, assumptions)
            }

            fn core(&self, fact: &CResourceFact) -> Option<CResourceFact> {
                access_mode_core(fact)
            }

            fn observable_facts(
                &self,
                facts: &[&CResourceFact],
                _assumptions: &Assumptions,
            ) -> Vec<Proposition> {
                same_family_separate_facts(facts)
            }
        }
    };
}

impl_exact_resource_algebra!(TokenResourceAlgebra, ResourceFamily::Token);
impl_exact_resource_algebra!(CompositeResourceAlgebra, ResourceFamily::Composite);

fn resource_fact_read_core_range(resource: &CResourceFact) -> Option<CMemoryRange> {
    match resource.core()? {
        CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::View(CResource::Composite { .. } | CResource::Token { .. })
        | CResourceFact::Own(_) => None,
    }
}

fn memory_resource_fact_permits_read(
    resource: &CResourceFact,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    resource_fact_read_core_range(resource).is_some_and(|range| {
        assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
        )
    })
}

fn memory_resource_fact_permits_write(
    resource: &CResourceFact,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    match resource {
        CResourceFact::Own(CResource::Memory(range)) => assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
        ),
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. })
        | CResourceFact::View(_) => false,
    }
}

fn pointer_has_structural_range_base(pointer: &Pointer, base: &Pointer) -> bool {
    if pointer.block != base.block {
        return false;
    }
    if super::assumptions::pointers_equal_ignoring_memories(pointer, base) {
        return true;
    }
    matches!(
        &pointer.offset,
        PointerOffsetTerm::Add(left, right)
            if super::assumptions::pointers_equal_ignoring_memories(
                &Pointer {
                    block: pointer.block.clone(),
                    offset: left.as_ref().clone(),
                },
                base,
            ) || super::assumptions::pointers_equal_ignoring_memories(
                &Pointer {
                    block: pointer.block.clone(),
                    offset: right.as_ref().clone(),
                },
                base,
            )
    )
}

/// Range endpoints compare like ordinary terms, and additionally two loads
/// of one pointer are equal when the pointed-to cell is provably unchanged
/// between their snapshots — a range spelled through metadata loads then
/// survives writes to unrelated cells.
fn range_endpoint_terms_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    fn loads_bridged(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &Assumptions,
    ) -> bool {
        // The load-unchanged check re-enters separation reasoning, which can
        // re-enter range comparison; guard against unbounded mutual
        // recursion rather than relying on structural depth.
        thread_local! {
            static ENDPOINT_BRIDGE_ACTIVE: std::cell::Cell<bool> =
                const { std::cell::Cell::new(false) };
        }
        if let (
            Bitvector32Term::MemoryLoad(left_memory, left_pointer),
            Bitvector32Term::MemoryLoad(right_memory, right_pointer),
        ) = (left, right)
            && left_pointer == right_pointer
        {
            if ENDPOINT_BRIDGE_ACTIVE.with(std::cell::Cell::get) {
                super::assumptions::note_search_truncation();
                return false;
            }
            ENDPOINT_BRIDGE_ACTIVE.with(|active| active.set(true));
            let bridged = super::api::c_memory_load_is_unchanged(
                left_memory,
                right_memory,
                left_pointer,
                assumptions,
            ) || super::api::c_memory_load_is_unchanged(
                right_memory,
                left_memory,
                left_pointer,
                assumptions,
            );
            ENDPOINT_BRIDGE_ACTIVE.with(|active| active.set(false));
            return bridged;
        }
        false
    }
    if loads_bridged(left, right, assumptions) {
        return true;
    }
    // Structural descent covers the common affine endpoint spellings
    // (base + load, load - base, load * scale).
    let structurally_bridged = match (left, right) {
        (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
        | (
            Bitvector32Term::Subtract(left_a, left_b),
            Bitvector32Term::Subtract(right_a, right_b),
        )
        | (
            Bitvector32Term::Multiply(left_a, left_b),
            Bitvector32Term::Multiply(right_a, right_b),
        ) => {
            range_endpoint_terms_equal(left_a, right_a, assumptions)
                && range_endpoint_terms_equal(left_b, right_b, assumptions)
        }
        _ => false,
    };
    structurally_bridged
        || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
}

/// Pointer bases compare with the same load bridging as range endpoints:
/// two spellings of one loaded base pointer are equal when the loaded cell
/// is provably unchanged between their snapshots.
fn pointer_bases_equal_with_load_bridging(
    left: &Pointer,
    right: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    left.block == right.block
        && pointer_offsets_equal_with_load_bridging(&left.offset, &right.offset, assumptions)
}

fn pointer_offsets_equal_with_load_bridging(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
            pointer_offsets_equal_with_load_bridging(left_a, right_a, assumptions)
                && pointer_offsets_equal_with_load_bridging(left_b, right_b, assumptions)
        }
        (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) => {
            left_width == right_width
                && range_endpoint_terms_equal(left_value, right_value, assumptions)
        }
        _ => false,
    }
}

pub(super) fn memory_range_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    if available == required {
        return true;
    }
    if available.base().blocks_proven_distinct(required.base()) {
        return false;
    }
    if assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
        available, required,
    ) {
        return false;
    }
    if (pointers_proven_equal_for_memory_resolution(available.base(), required.base(), assumptions)
        || pointer_bases_equal_with_load_bridging(available.base(), required.base(), assumptions))
        && range_endpoint_terms_equal(available.start(), required.start(), assumptions)
        && range_endpoint_terms_equal(available.end(), required.end(), assumptions)
    {
        return true;
    }
    if let Some(covers) = memory_range_structurally_covers(available, required) {
        return covers;
    }
    if super::assumptions::memory_range_contained_for_memory_resolution(
        required,
        available,
        assumptions,
    ) {
        return true;
    }
    assumptions.range_covered_by_fact_range(
        required,
        available.base(),
        available.start(),
        available.end(),
    )
}

fn memory_resource_fact_range(fact: &CResourceFact) -> Option<&CMemoryRange> {
    match fact {
        CResourceFact::Own(CResource::Memory(range))
        | CResourceFact::View(CResource::Memory(range)) => Some(range),
        CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. })
        | CResourceFact::View(CResource::Composite { .. } | CResource::Token { .. }) => None,
    }
}

fn memory_range_structurally_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
) -> Option<bool> {
    let base_delta = required.base().element_index_from_base(available.base())?;
    let available_start = available.start().as_const()? as i32;
    let available_end = available.end().as_const()? as i32;
    let required_start =
        Bitvector32Term::add(base_delta.clone(), required.start().clone()).as_const()? as i32;
    let required_end = Bitvector32Term::add(base_delta, required.end().clone()).as_const()? as i32;
    Some(available_start <= required_start && required_end <= available_end)
}

fn memory_ranges_structurally_disjoint(left: &CMemoryRange, right: &CMemoryRange) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return true;
    }
    let Some(base_delta) = right.base().element_index_from_base(left.base()) else {
        return false;
    };
    let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
        left.start().as_const().map(|value| value as i32),
        left.end().as_const().map(|value| value as i32),
        Bitvector32Term::add(base_delta.clone(), right.start().clone())
            .as_const()
            .map(|value| value as i32),
        Bitvector32Term::add(base_delta, right.end().clone())
            .as_const()
            .map(|value| value as i32),
    ) else {
        return false;
    };
    left_end < right_start || right_end < left_start
}

fn split_memory_range(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &Assumptions,
) -> Option<Vec<CMemoryRange>> {
    // Prefer the held range's own start spelling when the required base is
    // provably that address. A merely structural delta can contain an
    // equivalent load from a later memory snapshot; retaining it would create
    // a symbolic zero-length residue when the required range exhausts the
    // beginning of `available`.
    let available_start_pointer = available
        .base()
        .offset_by_int32_elements(available.start().clone());
    let base_delta = if pointers_proven_equal_for_memory_resolution(
        required.base(),
        &available_start_pointer,
        assumptions,
    ) {
        Some(available.start().clone())
    } else {
        required
            .base()
            .element_index_from_base(available.base())
            .or_else(|| {
                pointer_bases_equal_with_load_bridging(
                    required.base(),
                    available.base(),
                    assumptions,
                )
                .then_some(Bitvector32Term::Constant(0))
            })
    }?;
    let required_start = Bitvector32Term::add(base_delta.clone(), required.start().clone());
    let required_end = Bitvector32Term::add(base_delta, required.end().clone());
    let mut residues = Vec::new();
    if !bitvector_terms_proven_equal(available.start(), &required_start, assumptions)
        && !range_endpoint_terms_equal(available.start(), &required_start, assumptions)
    {
        residues.push(CMemoryRange::new(
            available.base().clone(),
            available.start().clone(),
            required_start.clone(),
        ));
    }
    if !bitvector_terms_proven_equal(&required_end, available.end(), assumptions)
        && !range_endpoint_terms_equal(&required_end, available.end(), assumptions)
    {
        residues.push(CMemoryRange::new(
            available.base().clone(),
            required_end,
            available.end().clone(),
        ));
    }
    Some(residues)
}

fn memory_ranges_proven_overlapping(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    if left.base().blocks_proven_distinct(right.base()) {
        return false;
    }
    if assumptions
        .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(left, right)
    {
        return false;
    }
    let Some(base_delta) = right.base().element_index_from_base(left.base()) else {
        return false;
    };
    let right_start = Bitvector32Term::add(base_delta.clone(), right.start().clone());
    let right_end = Bitvector32Term::add(base_delta, right.end().clone());

    assumptions.decide(&ConditionTerm::signed_less_than(
        left.start().clone(),
        right_end,
    )) == Some(true)
        && assumptions.decide(&ConditionTerm::signed_less_than(
            right_start,
            left.end().clone(),
        )) == Some(true)
}

impl CResource {
    pub fn family(&self) -> ResourceFamily {
        match self {
            Self::Memory(_) => ResourceFamily::Memory,
            Self::Composite { .. } => ResourceFamily::Composite,
            Self::Token { .. } => ResourceFamily::Token,
        }
    }
}

impl CResourceFact {
    pub const ALLOCATION_RESOURCE_NAME: &'static str = "allocation";

    pub fn own_memory(range: CMemoryRange) -> Self {
        Self::Own(CResource::Memory(range))
    }

    pub fn view_memory(range: CMemoryRange) -> Self {
        Self::View(CResource::Memory(range))
    }

    pub fn own_composite(name: String, arguments: Vec<CValue>) -> Self {
        Self::Own(CResource::Composite { name, arguments })
    }

    pub fn view_composite(name: String, arguments: Vec<CValue>) -> Self {
        Self::View(CResource::Composite { name, arguments })
    }

    pub fn own_token(name: String, arguments: Vec<CValue>) -> Self {
        Self::Own(CResource::Token { name, arguments })
    }

    pub fn own_allocation(base: Pointer, bytes: impl Into<Bitvector32Term>) -> Self {
        let bytes = bytes.into();
        Self::own_token(
            Self::ALLOCATION_RESOURCE_NAME.to_string(),
            vec![CValue::Pointer(base), int32(bytes)],
        )
    }

    pub fn allocation(&self) -> Option<(&Pointer, &Bitvector32Term)> {
        let Self::Own(CResource::Token { name, arguments }) = self else {
            return None;
        };
        if name != Self::ALLOCATION_RESOURCE_NAME {
            return None;
        }
        let [CValue::Pointer(base), CValue::Int32(bytes)] = arguments.as_slice() else {
            return None;
        };
        Some((base, bytes))
    }

    pub(super) fn may_refer_to_memory_block(&self, block: &PointerBlock) -> bool {
        match self.resource() {
            CResource::Memory(range) => &range.base().block == block,
            CResource::Composite { arguments, .. } => arguments.iter().any(
                |argument| matches!(argument, CValue::Pointer(pointer) if &pointer.block == block),
            ),
            CResource::Token { .. } => false,
        }
    }

    pub(super) fn is_proven_separate_from_allocation(
        &self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        assumptions: &Assumptions,
    ) -> bool {
        let Some(element_count) = super::reasoning::int32_element_count_from_bytes(bytes) else {
            return false;
        };
        let allocation_memory = CResource::Memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            element_count,
        ));
        assumptions.proves(&Proposition::CResourceSeparate {
            left: allocation_memory,
            right: self.resource().clone(),
        })
    }

    pub fn view_token(name: String, arguments: Vec<CValue>) -> Self {
        Self::View(CResource::Token { name, arguments })
    }

    pub fn resource(&self) -> &CResource {
        match self {
            Self::Own(resource) | Self::View(resource) => resource,
        }
    }

    pub fn is_own(&self) -> bool {
        matches!(self, Self::Own(_))
    }

    pub fn is_view(&self) -> bool {
        matches!(self, Self::View(_))
    }

    pub fn family(&self) -> ResourceFamily {
        self.resource().family()
    }

    pub fn core(&self) -> Option<Self> {
        resource_family_algebra(self.family()).core(self)
    }

    pub fn memory_own_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range)) => Some(range),
            Self::Own(CResource::Composite { .. } | CResource::Token { .. }) | Self::View(_) => {
                None
            }
        }
    }

    pub fn memory_view_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::View(CResource::Memory(range)) => Some(range),
            Self::View(CResource::Composite { .. } | CResource::Token { .. }) | Self::Own(_) => {
                None
            }
        }
    }

    pub fn memory_range(&self) -> Option<&CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range)) | Self::View(CResource::Memory(range)) => {
                Some(range)
            }
            Self::Own(CResource::Composite { .. } | CResource::Token { .. })
            | Self::View(CResource::Composite { .. } | CResource::Token { .. }) => None,
        }
    }

    pub fn owned_resource(&self) -> Option<&CResource> {
        match self {
            Self::Own(resource) => Some(resource),
            Self::View(_) => None,
        }
    }
}

fn combine_memory_resource_facts(
    left: &CResourceFact,
    right: &CResourceFact,
    assumptions: &Assumptions,
) -> Option<CResourceFact> {
    if let (Some(left_range), Some(right_range)) = (
        memory_resource_fact_range(left),
        memory_resource_fact_range(right),
    ) && memory_ranges_structurally_disjoint(left_range, right_range)
    {
        return None;
    }
    match (left, right) {
        _ if memory_resource_fact_entails(left, right, assumptions) => Some(left.clone()),
        _ if memory_resource_fact_entails(right, left, assumptions) => Some(right.clone()),
        (
            CResourceFact::View(CResource::Memory(left)),
            CResourceFact::View(CResource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceFact::view_memory),
        (
            CResourceFact::Own(CResource::Memory(left)),
            CResourceFact::Own(CResource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceFact::own_memory),
        _ => None,
    }
}

fn merge_memory_ranges(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &Assumptions,
) -> Option<CMemoryRange> {
    if left.base() != right.base() {
        return None;
    }
    if left.end() == right.start()
        || bitvector_terms_proven_equal(left.end(), right.start(), assumptions)
    {
        return Some(CMemoryRange::new(
            left.base().clone(),
            left.start().clone(),
            right.end().clone(),
        ));
    }
    if right.end() == left.start()
        || bitvector_terms_proven_equal(right.end(), left.start(), assumptions)
    {
        return Some(CMemoryRange::new(
            left.base().clone(),
            right.start().clone(),
            left.end().clone(),
        ));
    }
    None
}

fn bitvector_terms_proven_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &Assumptions,
) -> bool {
    left == right
        || assumptions.decide(&ConditionTerm::equal(left.clone(), right.clone())) == Some(true)
        || assumptions.bitvector_terms_equal_from_facts(left, right)
}

impl Theorem {
    pub(super) fn new(proposition: Proposition) -> Self {
        Self { proposition }
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

impl PropositionDerivation {
    pub fn conclusion(&self) -> &Proposition {
        &self.conclusion
    }

    pub fn context_premises(&self) -> Vec<Proposition> {
        let mut premises = BTreeSet::new();
        self.collect_context_premises(&mut premises);
        premises.into_iter().collect()
    }

    fn collect_context_premises(&self, premises: &mut BTreeSet<Proposition>) {
        fn collect_local_assumptions(
            proposition: &Proposition,
            assumptions: &mut BTreeSet<Proposition>,
        ) {
            if let Proposition::And(left, right) = proposition {
                collect_local_assumptions(left, assumptions);
                collect_local_assumptions(right, assumptions);
            } else {
                assumptions.insert(proposition.clone());
            }
        }

        match &self.rule {
            PropositionDerivationRule::ContextFree => {}
            PropositionDerivationRule::ContextualAtomic {
                premises: required, ..
            }
            | PropositionDerivationRule::Explosion { premises: required } => {
                premises.extend(required.pure_facts());
            }
            PropositionDerivationRule::And { left, right } => {
                left.collect_context_premises(premises);
                right.collect_context_premises(premises);
            }
            PropositionDerivationRule::OrLeft(proof)
            | PropositionDerivationRule::OrRight(proof)
            | PropositionDerivationRule::DoubleNegation(proof)
            | PropositionDerivationRule::ImpliesFalseAntecedent(proof)
            | PropositionDerivationRule::ForAllBody(proof) => {
                proof.collect_context_premises(premises);
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let mut body_premises = BTreeSet::new();
                body.collect_context_premises(&mut body_premises);
                let mut local_assumptions = BTreeSet::new();
                collect_local_assumptions(antecedent, &mut local_assumptions);
                for local in local_assumptions {
                    body_premises.remove(&local);
                }
                premises.extend(body_premises);
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                for instance in instances {
                    instance.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::FiniteContextSplit {
                premises: range_premises,
                instances,
                ..
            } => {
                premises.extend(range_premises.pure_facts());
                for instance in instances {
                    instance.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::UpperBoundSplit {
                bound,
                variable,
                pivot,
                below,
                at,
            } => {
                premises.insert(Proposition::ConditionIs(bound.clone(), true));
                let variable = Bitvector32Term::Variable(*variable);
                for (proof, local) in [
                    (
                        below,
                        ConditionTerm::signed_less_than(variable.clone(), pivot.clone()),
                    ),
                    (at, ConditionTerm::equal(variable, pivot.clone())),
                ] {
                    let mut case_premises = BTreeSet::new();
                    proof.collect_context_premises(&mut case_premises);
                    case_premises.remove(&Proposition::ConditionIs(local, true));
                    premises.extend(case_premises);
                }
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                premises.insert(disjunction.clone());
                let mut case_propositions = Vec::new();
                collect_or_cases(disjunction, &mut case_propositions);
                for (case, local) in cases.iter().zip(case_propositions) {
                    let mut case_premises = BTreeSet::new();
                    case.collect_context_premises(&mut case_premises);
                    let mut local_assumptions = BTreeSet::new();
                    collect_local_assumptions(&local, &mut local_assumptions);
                    for local in local_assumptions {
                        case_premises.remove(&local);
                    }
                    premises.extend(case_premises);
                }
            }
        }
    }
}

impl Default for ExecutionBudget {
    fn default() -> Self {
        Self {
            expression_steps: 10_000,
            statement_steps: 10_000,
            function_calls: 1_000,
            loop_unrolls: 256,
            paths: 10_000,
            next_opaque_call: 0,
            next_verification_variable: 1_000_000,
        }
    }
}

impl ExecutionBudget {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_expression_steps(mut self, expression_steps: usize) -> Self {
        self.expression_steps = expression_steps;
        self
    }

    pub fn with_statement_steps(mut self, statement_steps: usize) -> Self {
        self.statement_steps = statement_steps;
        self
    }

    pub fn with_function_calls(mut self, function_calls: usize) -> Self {
        self.function_calls = function_calls;
        self
    }

    pub fn with_loop_unrolls(mut self, loop_unrolls: usize) -> Self {
        self.loop_unrolls = loop_unrolls;
        self
    }

    pub fn with_paths(mut self, paths: usize) -> Self {
        self.paths = paths;
        self
    }

    pub(crate) fn with_next_opaque_call(mut self, next_opaque_call: u64) -> Self {
        self.next_opaque_call = next_opaque_call;
        self
    }

    pub(crate) fn next_opaque_call(&self) -> u64 {
        self.next_opaque_call
    }

    pub(crate) fn with_next_verification_variable(
        mut self,
        next_verification_variable: u64,
    ) -> Self {
        self.next_verification_variable = 1_000_000 + next_verification_variable;
        self
    }

    pub(crate) fn next_verification_variable(&self) -> u64 {
        self.next_verification_variable - 1_000_000
    }

    pub(super) fn consume_expression_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.expression_steps, ExecutionLimit::ExpressionSteps)
    }

    pub(super) fn consume_statement_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.statement_steps, ExecutionLimit::StatementSteps)
    }

    pub(super) fn consume_function_call(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.function_calls, ExecutionLimit::FunctionCalls)
    }

    pub(super) fn consume_loop_unroll(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.loop_unrolls, ExecutionLimit::LoopUnrolls)
    }

    pub(super) fn consume_paths(&mut self, paths: usize) -> ExecutionResult<()> {
        if crate::instrumentation::deadline_exceeded() {
            return Err(ExecutionLimit::Deadline);
        }
        if self.paths < paths {
            return Err(ExecutionLimit::Paths);
        }
        self.paths -= paths;
        Ok(())
    }
}

pub(super) type ExecutionResult<T> = Result<T, ExecutionLimit>;

pub(super) fn consume_budget(remaining: &mut usize, limit: ExecutionLimit) -> ExecutionResult<()> {
    if crate::instrumentation::deadline_exceeded() {
        return Err(ExecutionLimit::Deadline);
    }
    if *remaining == 0 {
        return Err(limit);
    }
    *remaining -= 1;
    Ok(())
}
