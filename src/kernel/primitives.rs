use super::api::{int32, uint8};
use super::reasoning::{
    instantiate_range_fold_step, int32_element_index_from_offset, pointers_proven_distinct,
    signed_bitvector_constant, signed_i64_bitvector_constant,
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
    MemoryLoad(Box<CMemory>, Box<Pointer>),
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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Pointer {
    pub block: String,
    pub offset: PointerOffsetTerm,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CValue {
    Int32(Bitvector32Term),
    UInt8(Bitvector32Term),
    Pointer(Pointer),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CType {
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
        arguments: Vec<SpecExpression>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CStatement {
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
    pub(super) resource_requires: Vec<CResourceSpec>,
    pub(super) resource_ensures: Vec<CResourceSpec>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionSpecification {
    pub(super) state: CState,
    pub(super) arguments: Vec<CExpression>,
    pub(super) requires: Vec<Proposition>,
    pub(super) outcome: CFunctionOutcome,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CFunctionEnvironment {
    pub(super) functions: BTreeMap<String, CFunction>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CUndefinedBehavior {
    SignedOverflow,
    DivisionByZero,
    InvalidShift,
    InvalidMemory,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CRuntimeError {
    UnboundVariable(String),
    UnknownFunction(String),
    TypeMismatch,
    WrongArity {
        expected: usize,
        actual: usize,
    },
    MissingReturn,
    MissingResource {
        resource: CResourceElement,
    },
    DuplicateResource {
        resource: CResourceElement,
    },
    OverlappingWriteResources {
        left: Box<CMemoryRange>,
        right: Box<CMemoryRange>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum ExecutionLimit {
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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CExpressionOutcome {
    Value(CValue),
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
    Return { value: CValue, state: CState },
    UndefinedBehavior(CUndefinedBehavior),
    RuntimeError(CRuntimeError),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CFunctionOutcome {
    Return { value: CValue, state: CState },
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
    ArrayObject { element_type: CType, length: u32 },
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CMemory {
    pub(super) blocks: BTreeMap<String, CBlock>,
    pub(super) cells: BTreeMap<Pointer, CValue>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CBlock {
    pub(super) size: u32,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CState {
    pub(super) locals: CLocalEnvironment,
    pub(super) memory: CMemory,
    pub(super) resources: ResourceContext,
}

#[derive(Clone, Debug, Default, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ResourceContext {
    pub(super) elements: Vec<CResourceElement>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum CResourceElement {
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
    DuplicateOwnedResourceElement(CResourceElement),
    OverlappingWriteResources {
        left: CMemoryRange,
        right: CMemoryRange,
    },
}

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
    CStatementExecutes {
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
    CFunctionSatisfiesSpecification {
        function: CFunction,
        specification: CFunctionSpecification,
    },
    CMemoryLoads {
        memory: CMemory,
        pointer: Pointer,
        outcome: CExpressionOutcome,
    },
    CMemoryCanLoad {
        memory: CMemory,
        pointer: Pointer,
        byte_width: u32,
    },
    CMemoryCanStore {
        memory: CMemory,
        pointer: Pointer,
        byte_width: u32,
    },
    CMemoryValidRange {
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

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Assumptions {
    pub(super) condition_facts: BTreeMap<ConditionTerm, bool>,
    pub(super) prop_facts: BTreeSet<Proposition>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ProofObligation {
    pub(super) proposition: Proposition,
    pub(super) context: Option<String>,
    pub(super) assumable: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct PathFact {
    pub(super) proposition: Proposition,
    pub(super) public: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecution {
    pub(super) paths: Vec<SymbolicCExecutionPath>,
    pub(super) limit: Option<ExecutionLimit>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolicCExecutionPath {
    pub(super) facts: Vec<PathFact>,
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) theorem: Theorem,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CExpressionPath {
    pub(super) outcome: CExpressionOutcome,
    pub(super) facts: Vec<PathFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CLValuePath {
    pub(super) outcome: CLValueOutcome,
    pub(super) facts: Vec<PathFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CStatementExecutionPath {
    pub(super) outcome: CStatementOutcome,
    pub(super) facts: Vec<PathFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CFunctionPath {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: Vec<PathFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CArgumentsPath {
    pub(super) values: Vec<CValue>,
    pub(super) outcome: Option<CFunctionOutcome>,
    pub(super) facts: Vec<PathFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct VerificationVariableGenerator {
    pub(super) next: u64,
}

impl VerificationVariableGenerator {
    pub(super) fn new(start: u64) -> Self {
        Self { next: start }
    }

    pub(super) fn next(&mut self) -> Variable {
        let variable = Variable(self.next);
        self.next += 1;
        variable
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

    pub(super) fn as_const(&self) -> Option<u32> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) | Self::MemoryLoad(_, _) => None,
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
            (Self::Constant(constant), Self::Subtract(base, subtrahend))
                if subtrahend.as_ref() == &Self::Constant(*constant) =>
            {
                base.as_ref().clone()
            }
            (Self::Subtract(base, subtrahend), Self::Constant(constant))
                if subtrahend.as_ref() == &Self::Constant(*constant) =>
            {
                base.as_ref().clone()
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
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => Self::Constant(*left ^ *right),
            (_, Self::Constant(0)) => left,
            (Self::Constant(0), _) => right,
            _ if left == right => Self::Constant(0),
            _ => Self::BitwiseXor(Box::new(left), Box::new(right)),
        }
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
}

impl CType {
    pub(super) fn accepts(self, value: &CValue) -> bool {
        matches!(
            (self, value),
            (Self::Int32, CValue::Int32(_))
                | (Self::UInt8, CValue::UInt8(_))
                | (Self::Int32Pointer, CValue::Pointer(_))
                | (Self::UInt8Pointer, CValue::Pointer(_))
        )
    }

    pub fn byte_width(self) -> u32 {
        match self {
            Self::Int32 => 4,
            Self::UInt8 => 1,
            Self::Int32Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int32Array(length) => length.checked_mul(4).unwrap_or(u32::MAX),
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
            Self::Int32(_) => CType::Int32,
            Self::UInt8(_) => CType::UInt8,
            Self::Pointer(_) => CType::Int32Pointer,
        }
    }

    pub(super) fn byte_width(&self) -> u32 {
        match self {
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
    #[cfg_attr(not(test), allow(dead_code))]
    pub(super) fn offset_by_int32_elements(&self, elements: Bitvector32Term) -> Self {
        self.offset_by_elements(elements, 4)
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

    pub(super) fn element_index_from_base(&self, base: &Self) -> Option<Bitvector32Term> {
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
            body,
            resource_requires: Vec::new(),
            resource_ensures: Vec::new(),
        }
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

    pub fn resource_requires(&self) -> &[CResourceSpec] {
        &self.resource_requires
    }

    pub fn resource_ensures(&self) -> &[CResourceSpec] {
        &self.resource_ensures
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
        Self { base, start, end }
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

impl CFunctionEnvironment {
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
            Some(CLocalBinding::ArrayObject { .. }) | None => None,
        }
    }

    pub(super) fn object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
        }
    }

    pub(super) fn scalar_object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
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
        Self { size }
    }

    pub fn size(&self) -> u32 {
        self.size
    }
}

impl CMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_block(mut self, block: impl Into<String>, size: u32) -> Self {
        self.blocks.insert(block.into(), CBlock::new(size));
        self
    }

    pub(super) fn with_loop_memory_havoc(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<String>,
    ) -> Self {
        // A loop body that may write memory can clobber, through some
        // pointer, any cell it can reach. Drop concrete cells outside the
        // preserved (scalar stack local) blocks so loop-head and post-loop
        // reads do not observe stale pre-loop values; anything that must
        // survive the loop has to be restated as a loop invariant. The
        // marker block additionally defeats symbolic cross-loop load
        // equality for the remaining symbolic memory.
        self.cells
            .retain(|pointer, _| preserved_blocks.contains(&pointer.block));
        self.blocks
            .insert(format!("havoc:{}", variable.0), CBlock::new(0));
        self
    }

    pub fn store(mut self, pointer: Pointer, value: CValue) -> Self {
        self.cells.insert(pointer, value);
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

    pub(super) fn without_proven_distinct_cells(
        &self,
        pointer: &Pointer,
        assumptions: &Assumptions,
    ) -> Self {
        let mut memory = self.clone();
        memory.cells.retain(|cell_pointer, _| {
            cell_pointer.block != pointer.block
                || !pointers_proven_distinct(cell_pointer, pointer, assumptions)
        });
        memory
    }

    pub(super) fn without_possible_aliasing_cells(
        &self,
        pointer: &Pointer,
        assumptions: &Assumptions,
    ) -> Self {
        let mut memory = self.clone();
        memory.cells.retain(|cell_pointer, _| {
            cell_pointer.block != pointer.block
                || pointers_proven_distinct(cell_pointer, pointer, assumptions)
        });
        memory
    }

    pub(super) fn first_unresolved_same_block_cell(
        &self,
        pointer: &Pointer,
        assumptions: &Assumptions,
    ) -> Option<(Pointer, CValue)> {
        self.cells
            .iter()
            .find(|(cell_pointer, _)| {
                cell_pointer.block == pointer.block
                    && *cell_pointer != pointer
                    && assumptions
                        .decide(&ConditionTerm::pointer_offset_equal(
                            cell_pointer.offset.clone(),
                            pointer.offset.clone(),
                        ))
                        .is_none()
            })
            .map(|(pointer, value)| (pointer.clone(), value.clone()))
    }

    pub(super) fn local_pointer(name: &str) -> Pointer {
        Pointer {
            block: format!("local:{name}"),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(super) fn has_block(&self, block: &str) -> bool {
        self.blocks.contains_key(block)
    }

    pub(super) fn can_load_concretely(&self, pointer: &Pointer, byte_width: u32) -> bool {
        self.cells.contains_key(pointer) || self.access_in_bounds(pointer, byte_width)
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
        offset
            .checked_add(byte_width)
            .is_some_and(|end| end <= block.size())
    }

    pub(super) fn symbolic_int32_load(&self, pointer: &Pointer) -> CValue {
        int32(Bitvector32Term::MemoryLoad(
            Box::new(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(super) fn symbolic_uint8_load(&self, pointer: &Pointer) -> CValue {
        uint8(Bitvector32Term::MemoryLoad(
            Box::new(self.clone()),
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
                Bitvector32Term::MemoryLoad(Box::new(self.clone()), Box::new(pointer.clone())),
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

    /// Adds a resource element without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_element` when proposition assumptions are
    /// available.
    pub fn unchecked_with_element(mut self, element: CResourceElement) -> Self {
        self.elements.push(element);
        self
    }

    /// Adds resource elements without checking validity or normalizing the
    /// context.
    ///
    /// Prefer `try_compose_with_elements` when proposition assumptions are
    /// available.
    pub fn unchecked_with_elements(
        mut self,
        elements: impl IntoIterator<Item = CResourceElement>,
    ) -> Self {
        self.elements.extend(elements);
        self
    }

    pub fn try_compose_with_element(
        self,
        element: CResourceElement,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        self.try_compose_with_elements(std::iter::once(element), assumptions)
    }

    pub fn try_compose_with_elements(
        self,
        elements: impl IntoIterator<Item = CResourceElement>,
        assumptions: &Assumptions,
    ) -> Result<Self, ResourceContextValidityError> {
        let context = self.unchecked_with_elements(elements);
        if let Some(error) = context.validity_error(assumptions) {
            return Err(error);
        }
        Ok(context.normalized(assumptions))
    }

    pub fn elements(&self) -> &[CResourceElement] {
        &self.elements
    }

    pub fn validity_error(
        &self,
        assumptions: &Assumptions,
    ) -> Option<ResourceContextValidityError> {
        if let Some(resource) = self.duplicate_owned_element() {
            return Some(ResourceContextValidityError::DuplicateOwnedResourceElement(
                resource.clone(),
            ));
        }
        if let Some((left, right)) = self.overlapping_owned_memory_pair(assumptions) {
            return Some(ResourceContextValidityError::OverlappingWriteResources {
                left: left.clone(),
                right: right.clone(),
            });
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
        Ok(self.owned_memory_disjoint_facts())
    }

    pub fn has_multiple_owned_memory_resources(&self) -> bool {
        self.elements
            .iter()
            .filter(|resource| resource.memory_own_range().is_some())
            .take(2)
            .count()
            == 2
    }

    pub fn overlapping_owned_memory_pair(
        &self,
        assumptions: &Assumptions,
    ) -> Option<(&CMemoryRange, &CMemoryRange)> {
        for i in 0..self.elements.len() {
            let Some(left) = self.elements[i].memory_own_range() else {
                continue;
            };
            for candidate in &self.elements[i + 1..] {
                let Some(right) = candidate.memory_own_range() else {
                    continue;
                };
                if memory_ranges_proven_overlapping(left, right, assumptions) {
                    return Some((left, right));
                }
            }
        }
        None
    }

    fn owned_memory_disjoint_facts(&self) -> Vec<Proposition> {
        let owned = self
            .elements
            .iter()
            .filter_map(CResourceElement::memory_own_range)
            .collect::<Vec<_>>();
        let mut propositions = Vec::new();
        for i in 0..owned.len() {
            for right in &owned[i + 1..] {
                let left = owned[i];
                propositions.push(Proposition::CMemoryDisjoint {
                    left_base: left.base.clone(),
                    left_start: left.start.clone(),
                    left_end: left.end.clone(),
                    right_base: right.base.clone(),
                    right_start: right.start.clone(),
                    right_end: right.end.clone(),
                });
            }
        }
        propositions
    }

    pub fn duplicate_owned_element(&self) -> Option<&CResourceElement> {
        for i in 0..self.elements.len() {
            if !self.elements[i].is_owned_non_memory() {
                continue;
            }
            if self.elements[i + 1..]
                .iter()
                .any(|candidate| candidate == &self.elements[i])
            {
                return Some(&self.elements[i]);
            }
        }
        None
    }

    pub fn satisfies_element(&self, element: &CResourceElement, assumptions: &Assumptions) -> bool {
        self.elements
            .iter()
            .any(|available| resource_element_entails(available, element, assumptions))
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    pub(super) fn permits_memory_read(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> bool {
        self.elements
            .iter()
            .any(|resource| memory_element_permits_read(resource, pointer, byte_width, assumptions))
    }

    pub(super) fn permits_memory_write(
        &self,
        pointer: &Pointer,
        byte_width: u32,
        assumptions: &Assumptions,
    ) -> bool {
        self.elements.iter().any(|resource| {
            memory_element_permits_write(resource, pointer, byte_width, assumptions)
        })
    }

    pub fn without_element(
        self,
        element: &CResourceElement,
        assumptions: &Assumptions,
    ) -> Option<Self> {
        consume_element(self, element, assumptions)
    }

    pub(super) fn normalized(mut self, assumptions: &Assumptions) -> Self {
        let mut i = 0;
        while i < self.elements.len() {
            let mut changed = false;
            let mut j = i + 1;
            while j < self.elements.len() {
                if let Some(merged) =
                    combine_elements(&self.elements[i], &self.elements[j], assumptions)
                {
                    self.elements[i] = merged;
                    self.elements.remove(j);
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

fn resource_element_entails(
    available: &CResourceElement,
    required: &CResourceElement,
    assumptions: &Assumptions,
) -> bool {
    if available.family() != required.family() {
        return false;
    }
    match available.family() {
        ResourceFamily::Memory => memory_element_entails(available, required, assumptions),
        ResourceFamily::Composite | ResourceFamily::Token => {
            non_memory_element_entails(available, required)
        }
    }
}

fn consume_element(
    context: ResourceContext,
    required: &CResourceElement,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    match required.family() {
        ResourceFamily::Memory => consume_memory_element(context, required, assumptions),
        ResourceFamily::Composite | ResourceFamily::Token => {
            consume_non_memory_element(context, required, assumptions)
        }
    }
}

fn combine_elements(
    left: &CResourceElement,
    right: &CResourceElement,
    assumptions: &Assumptions,
) -> Option<CResourceElement> {
    if left.family() != right.family() {
        return None;
    }
    match left.family() {
        ResourceFamily::Memory => combine_memory_elements(left, right, assumptions),
        ResourceFamily::Composite | ResourceFamily::Token => {
            combine_non_memory_elements(left, right)
        }
    }
}

fn memory_element_entails(
    available: &CResourceElement,
    required: &CResourceElement,
    assumptions: &Assumptions,
) -> bool {
    match (available, required) {
        (_, _) if required.memory_view_range().is_some() => {
            let required = required.memory_view_range().expect("checked above");
            let Some(available) = resource_element_read_core_range(available) else {
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

fn consume_memory_element(
    mut context: ResourceContext,
    required: &CResourceElement,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    if let Some(required) = required.memory_view_range() {
        return context
            .elements
            .iter()
            .any(|candidate| {
                resource_element_read_core_range(candidate)
                    .is_some_and(|available| memory_range_covers(&available, required, assumptions))
            })
            .then(|| context.normalized(assumptions));
    }
    if let Some(required) = required.memory_own_range() {
        let index = context.elements.iter().position(|candidate| {
            candidate
                .memory_own_range()
                .is_some_and(|available| memory_range_covers(available, required, assumptions))
        })?;
        let available = context
            .elements
            .remove(index)
            .into_memory_own_range()
            .expect("own resource lookup ignored non-own resources");
        context.elements.extend(
            split_memory_range(&available, required, assumptions)?
                .into_iter()
                .map(CResourceElement::own_memory),
        );
        return Some(context.normalized(assumptions));
    }
    unreachable!("non-memory resource sent to memory resource consumer")
}

fn non_memory_element_entails(available: &CResourceElement, required: &CResourceElement) -> bool {
    match (available, required) {
        (CResourceElement::Own(available), CResourceElement::Own(required)) => {
            available == required
        }
        (
            CResourceElement::Own(available) | CResourceElement::View(available),
            CResourceElement::View(required),
        ) => available == required,
        _ => false,
    }
}

fn consume_non_memory_element(
    mut context: ResourceContext,
    required: &CResourceElement,
    assumptions: &Assumptions,
) -> Option<ResourceContext> {
    if matches!(required, CResourceElement::View(_)) {
        return context
            .elements
            .iter()
            .any(|candidate| non_memory_element_entails(candidate, required))
            .then(|| context.normalized(assumptions));
    }
    let index = context
        .elements
        .iter()
        .position(|candidate| candidate == required)?;
    context.elements.remove(index);
    Some(context.normalized(assumptions))
}

fn combine_non_memory_elements(
    left: &CResourceElement,
    right: &CResourceElement,
) -> Option<CResourceElement> {
    match (left, right) {
        (CResourceElement::Own(left), CResourceElement::View(right))
        | (CResourceElement::View(right), CResourceElement::Own(left))
            if left == right =>
        {
            Some(CResourceElement::Own(left.clone()))
        }
        (CResourceElement::View(left), CResourceElement::View(right)) if left == right => {
            Some(CResourceElement::View(left.clone()))
        }
        _ => None,
    }
}

fn resource_element_core(resource: &CResourceElement) -> Option<CResourceElement> {
    match resource {
        CResourceElement::Own(resource) | CResourceElement::View(resource) => {
            Some(CResourceElement::View(resource.clone()))
        }
    }
}

fn resource_element_read_core_range(resource: &CResourceElement) -> Option<CMemoryRange> {
    match resource.core()? {
        CResourceElement::View(CResource::Memory(range)) => Some(range),
        CResourceElement::View(CResource::Composite { .. } | CResource::Token { .. })
        | CResourceElement::Own(_) => None,
    }
}

fn memory_element_permits_read(
    resource: &CResourceElement,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    resource_element_read_core_range(resource).is_some_and(|range| {
        assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
        )
    })
}

fn memory_element_permits_write(
    resource: &CResourceElement,
    pointer: &Pointer,
    byte_width: u32,
    assumptions: &Assumptions,
) -> bool {
    match resource {
        CResourceElement::Own(CResource::Memory(range)) => assumptions.pointer_access_in_range(
            pointer,
            byte_width,
            range.base(),
            range.start(),
            range.end(),
        ),
        CResourceElement::Own(CResource::Composite { .. } | CResource::Token { .. })
        | CResourceElement::View(_) => false,
    }
}

fn memory_range_covers(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &Assumptions,
) -> bool {
    assumptions.range_covered_by_fact_range(
        required,
        available.base(),
        available.start(),
        available.end(),
    )
}

fn split_memory_range(
    available: &CMemoryRange,
    required: &CMemoryRange,
    assumptions: &Assumptions,
) -> Option<Vec<CMemoryRange>> {
    let base_delta = required.base().element_index_from_base(available.base())?;
    let required_start = Bitvector32Term::add(base_delta.clone(), required.start().clone());
    let required_end = Bitvector32Term::add(base_delta, required.end().clone());
    let mut residues = Vec::new();
    if !bitvector_terms_proven_equal(available.start(), &required_start, assumptions) {
        residues.push(CMemoryRange::new(
            available.base().clone(),
            available.start().clone(),
            required_start.clone(),
        ));
    }
    if !bitvector_terms_proven_equal(&required_end, available.end(), assumptions) {
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
    if left.base().block != right.base().block {
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

impl CResourceElement {
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

    pub fn is_owned_non_memory(&self) -> bool {
        matches!(
            self,
            Self::Own(CResource::Composite { .. } | CResource::Token { .. })
        )
    }

    pub fn family(&self) -> ResourceFamily {
        match self.resource() {
            CResource::Memory(_) => ResourceFamily::Memory,
            CResource::Composite { .. } => ResourceFamily::Composite,
            CResource::Token { .. } => ResourceFamily::Token,
        }
    }

    pub fn core(&self) -> Option<Self> {
        resource_element_core(self)
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

    fn into_memory_own_range(self) -> Option<CMemoryRange> {
        match self {
            Self::Own(CResource::Memory(range)) => Some(range),
            Self::Own(CResource::Composite { .. } | CResource::Token { .. }) | Self::View(_) => {
                None
            }
        }
    }
}

fn combine_memory_elements(
    left: &CResourceElement,
    right: &CResourceElement,
    assumptions: &Assumptions,
) -> Option<CResourceElement> {
    match (left, right) {
        _ if memory_element_entails(left, right, assumptions) => Some(left.clone()),
        _ if memory_element_entails(right, left, assumptions) => Some(right.clone()),
        (
            CResourceElement::View(CResource::Memory(left)),
            CResourceElement::View(CResource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceElement::view_memory),
        (
            CResourceElement::Own(CResource::Memory(left)),
            CResourceElement::Own(CResource::Memory(right)),
        ) => merge_memory_ranges(left, right, assumptions).map(CResourceElement::own_memory),
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
    if bitvector_terms_proven_equal(left.end(), right.start(), assumptions) {
        return Some(CMemoryRange::new(
            left.base().clone(),
            left.start().clone(),
            right.end().clone(),
        ));
    }
    if bitvector_terms_proven_equal(right.end(), left.start(), assumptions) {
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

impl Default for ExecutionBudget {
    fn default() -> Self {
        Self {
            expression_steps: 10_000,
            statement_steps: 10_000,
            function_calls: 1_000,
            loop_unrolls: 256,
            paths: 10_000,
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
        if self.paths < paths {
            return Err(ExecutionLimit::Paths);
        }
        self.paths -= paths;
        Ok(())
    }
}

pub(super) type ExecutionResult<T> = Result<T, ExecutionLimit>;

pub(super) fn consume_budget(remaining: &mut usize, limit: ExecutionLimit) -> ExecutionResult<()> {
    if *remaining == 0 {
        return Err(limit);
    }
    *remaining -= 1;
    Ok(())
}
